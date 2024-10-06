#!/usr/bin/env python3
import pexpect
import time
import logging
import xml.etree.ElementTree as ET
from bitarray import bitarray
import binascii
from pathlib import Path
from zipfile import ZipFile
import sys

# Set up logging
logging.basicConfig(level=logging.INFO)

# Define Bluetooth characteristics
characteristics = {
    "machine_status": ["5a401524-ab2e-2548-c435-08c300000710", "0x000b"],
    "barista_mode": ["5a401530-ab2e-2548-c435-08c300000710", "0x0017"],
    "product_progress": ["5a401527-ab2e-2548-c435-08c300000710", "0x001a"],
    "heartbeat": ["5a401529-ab2e-2548-c435-08c300000710", "0x0011"],
    "heartbeat_read": ["5a401538-ab2e-2548-c435-08c300000710", "0x0032"],
    "start_product": ["5a401525-ab2e-2548-c435-08c300000710", "0x000e"],
    "statistics_command": ["5A401534-ab2e-2548-c435-08c300000710", "0x0026"],
    "statistics_data": ["5A401534-ab2e-2548-c435-08c300000710", "0x0029"],
    "uart_tx": ["5a401625-ab2e-2548-c435-08c300000710", "0x0039"],
    "uart_rx": ["5a401624-ab2e-2548-c435-08c300000710", "0x0036"],
    "read_stat": ["5a401533-ab2e-2548-c435-08c300000710", "0x000a"],
    "manufacturer_data": ["5a401531-ab2e-2548-c435-08c300000710", "0x001d"]
}

# Define the Bluetooth device address
DEVICE = sys.argv[1]

# JuraEncoder class for encoding/decoding Jura-specific data
class JuraEncoder:
    def __init__(self):
        self.base_layout = bitarray('01011011')

    def tojura(self, letter, hex=0):
        if len(letter) != 1:
            raise ValueError('Needs a single byte')
        c = bitarray()
        c.frombytes(letter.encode())
        c = c[-8:]
        c = c[2:4] + c[0:2] + c[6:8] + c[4:6]
        c = c[4:] + c[:4]
        bytes = [self.base_layout.copy() for _ in range(4)]
        hex_code = ""
        for i in range(4):
            bytes[i][2] = c[i * 2]
            bytes[i][5] = c[i * 2 + 1]
            if hex:
                hex_code += binascii.hexlify(bytes[i].tobytes()).decode() + " "
        return hex_code[:-1] if hex else bytes

    def fromjura(self, bytes, hex=0):
        if hex:
            bytes = [bitarray('{0:08b}'.format(int(binascii.unhexlify(j)[0]))) for j in bytes.split()]
        if len(bytes) != 4:
            raise ValueError('Needs an array of size 4')
        out = bitarray(8)
        for i in range(4):
            out[i * 2] = bytes[i][2]
            out[i * 2 + 1] = bytes[i][5]
        out = out[4:] + out[:4]
        out = out[2:4] + out[0:2] + out[6:8] + out[4:6]
        return out.tobytes().decode()

# BtEncoder class for encoding/decoding Bluetooth data
class BtEncoder:
    def __init__(self):
        self.numbers1 = [14, 4, 3, 2, 1, 13, 8, 11, 6, 15, 12, 7, 10, 5, 0, 9]
        self.numbers2 = [10, 6, 13, 12, 14, 11, 1, 9, 15, 7, 0, 5, 3, 2, 4, 8]

    def hexStrToInt(self, hexStr):
        return [int(hexStr[i:i+2], 16) for i in range(0, len(hexStr), 3)]

    def mod256(self, i):
        return i % 256

    def shuffle(self, dataNibble, nibbleCount, keyLeftNibbel, keyRightNibbel):
        i5 = self.mod256(nibbleCount >> 4)
        tmp1 = self.numbers1[self.mod256(dataNibble + nibbleCount + keyLeftNibbel) % 16]
        tmp2 = self.numbers2[self.mod256(tmp1 + keyRightNibbel + i5 - nibbleCount - keyLeftNibbel) % 16]
        tmp3 = self.numbers1[self.mod256(tmp2 + keyLeftNibbel + nibbleCount - keyRightNibbel - i5) % 16]
        return self.mod256(tmp3 - nibbleCount - keyLeftNibbel) % 16

    def encDecBytes(self, data, key):
        key = int(key, 16)
        result = []
        keyLeftNibbel = key >> 4
        keyRightNibbel = key & 15
        nibbelCount = 0
        for d in data:
            dataLeftNibbel = d >> 4
            dataRightNibbel = d & 15
            resultLeftNibbel = self.shuffle(dataLeftNibbel, nibbelCount, keyLeftNibbel, keyRightNibbel)
            resultRightNibbel = self.shuffle(dataRightNibbel, nibbelCount + 1, keyLeftNibbel, keyRightNibbel)
            result.append((resultLeftNibbel << 4) | resultRightNibbel)
            nibbelCount += 2
        logging.debug(f"ENCODED {''.join(['%02x' % d for d in data])} AS {''.join(['%02x' % d for d in result])}")
        return result

    def bruteforce_key(self, data):
        data = [int(d, 16) for d in data.split()]
        for key in range(256):
            key_hex = f"{key:02x}"
            result = self.encDecBytes(data, key_hex)
            if result[0] == int(key_hex, 16):
                logging.debug(f"key: {key_hex}")
                logging.debug(f"result: {result}")
                return key_hex
        return None

# Parse XML file and return root and namespace
def parse_xml(file_path):
    tree = ET.parse(file_path)
    root = tree.getroot()
    namespace = {'ns': 'http://www.top-tronic.com'}
    return root, namespace

# Extract product information from XML
def extract_products(root, namespace):
    return [{'Code': int(product.get('Code'), 16), 'Name': product.get('Name')} for product in root.findall('.//ns:PRODUCT', namespace)]

# Extract maintenance counters from XML
def extract_maintenance_counters(root, namespace, command):
    section = root.find(f'.//ns:BANK[@Command="{command}"]', namespace)
    return [textitem.get('Type') for textitem in section.findall('ns:TEXTITEM', namespace)]

# Extract alerts from XML
def extract_alerts(root, namespace):
    alerts = [None] * (max(int(alert.get('Bit')) for alert in root.findall('.//ns:ALERT', namespace)) + 1)
    for alert in root.findall('.//ns:ALERT', namespace):
        alerts[int(alert.get('Bit'))] = alert.get('Name')
    return alerts

# Set up Bluetooth connection
def setup_connection(device, characteristics):
    logging.info("Run gatttool...")
    child = pexpect.spawn(f"gatttool -b {device} -I -t random")
    logging.info(f"Connecting to {device}")
    child.sendline("connect")
    child.expect("Connection successful", timeout=5)
    logging.info("Connected!")

    # Read initial data and decode key
    child.sendline(f"char-read-hnd {characteristics['machine_status'][1]}")
    child.expect(": ", timeout=5)
    data = child.readline().decode().strip()
    logging.debug(f"Initial data: {data}")
    key_dec = bt_encoder.bruteforce_key(data)
    logging.debug(f"Key: {key_dec}")

    data = [int(x, 16) for x in data.split()]
    decoded = bt_encoder.encDecBytes(data, key_dec)
    logging.debug(f"Decoded data as HEX: {' '.join(['%02x' % d for d in decoded])}")

    return child, key_dec

# Encode command with key
def encode_command(command, key_dec):
    encoded = bt_encoder.encDecBytes([int(x, 16) for x in command.split()], key_dec)
    return "".join(["%02x" % d for d in encoded])

# Read data until a specific value is ready
def read_data_until_ready(child, uuid, ready_value_index, value):
    hex_values = []
    while len(hex_values) < ready_value_index + 1 or hex_values[ready_value_index] == value:
        child.sendline(f"char-read-uuid {uuid}")
        child.expect(": ")
        time.sleep(0.5)
        data = child.readline().decode().strip()
        value_part = data.split('value: ')[1].strip()
        hex_values = value_part.split()
        logging.debug(f"Read data while waiting to be ready: {value_part}")
    return value_part

# Read and decode statistics data
def read_and_decode_statistics(child, command, key_dec, characteristics):
    child.sendline(f"char-write-req {characteristics['statistics_command'][1]} {command}")
    read_data_until_ready(child, characteristics['read_stat'][0], 1, "e1")
    child.sendline(f"char-read-hnd {characteristics['statistics_data'][1]}")
    child.expect(": ")
    data = child.readline().decode().strip()
    logging.debug(f"Statistics data: {data}")
    data = [int(x, 16) for x in data.split()]
    decoded = bt_encoder.encDecBytes(data, key_dec)
    logging.debug(f"Decoded statistics data: {decoded}")
    return decoded

# Get machine information from resources
def get_machine(number: str) -> dict:
    path = Path(__file__).parent / "resources.zip"
    with ZipFile(path) as f:
        with f.open("JOE_MACHINES.TXT") as txt:
            for line in txt:
                line = line.decode()
                if not line.startswith(number):
                    continue
                items = line.split(";")
                break
        root, namespace = parse_xml(f.open("machinefiles/" + items[2] + ".xml"))

    return {"model": items[1], "root": root, "namespace": namespace}

# Log statistics data
def log_statistics(decoded, products):
    for i, byte in enumerate(decoded):
        product_code = i
        product = next((product for product in products if product['Code'] == product_code), None)
        if product:
            product_name = product['Name']
            if byte == 65535:
                byte = 0
            logging.info(f"Product code: {product_code}, Product name: {product_name}, Byte: {byte}")

# Log maintenance data
def log_maintenance(decoded, maintenance_list, label):
    for i, count in enumerate(maintenance_list):
        if i < len(decoded):
            logging.info(f"{label}: {count}, Value: {decoded[i]}")

# Load characteristics from JSON file
# Initialize encoders
bt_encoder = BtEncoder()
jura_encoder = JuraEncoder()

# Setup Bluetooth connection
child, key_dec = setup_connection(DEVICE, characteristics)

# Get machine model
value_part = read_data_until_ready(child, characteristics["manufacturer_data"][0], 2, "3d")
data = [int(x, 16) for x in value_part.split()]
logging.debug(f"Data: {data}")
model_id = data[5] * 256 + data[4]
logging.debug(f"Model ID: {model_id}")
decoded = bt_encoder.encDecBytes(data, key_dec)
logging.debug(f"Decoded statistics data: {decoded}")
machine = get_machine(str(model_id))
logging.info(f"Machine model: {machine['model']}")

# Parse XML file and extract necessary information
root = machine["root"]
namespace = machine["namespace"]

products = extract_products(root, namespace)
logging.debug(products)
cleaning_count = extract_maintenance_counters(root, namespace, "@TG:43")
cleaning_pct = extract_maintenance_counters(root, namespace, "@TG:C0")
logging.debug(cleaning_count)
logging.debug(cleaning_pct)
alerts = extract_alerts(root, namespace)
logging.debug(alerts)

# Get alerts
logging.info("Get alerts")
value_part = read_data_until_ready(child, characteristics["machine_status"][0], 2, "3d")
data = [int(x, 16) for x in value_part.split()]
decoded = bt_encoder.encDecBytes(data, key_dec)
logging.debug(f"Decoded statistics data: {decoded}")

# Check for active alerts
for i in range((len(decoded) - 1) * 8):
    offset_abs = (i >> 3) + 1
    offset_byte = 7 - (i & 0b111)
    if (decoded[offset_abs] >> offset_byte) & 0b1:
        logging.info(f"Alert active. Alert bit: {i} - {alerts[i]}")

# Read product count
logging.info("Read product count")
all_statistics = encode_command("2a 00 01 FF FF", key_dec)
decoded = read_and_decode_statistics(child, all_statistics, key_dec, characteristics)
decoded = [int("".join(["%02x" % d for d in decoded[i:i+3]]), 16) for i in range(0, len(decoded), 3)]
logging.debug(f"Current Statistics: {decoded}")
logging.info(f"Total coffee: {decoded[0]}")

# Log product information
log_statistics(decoded, products)

# Maintenance percents
logging.info("Read maintenance percents")
mnt_pct_statistics = encode_command("2a 00 08 01 00", key_dec)
decoded = read_and_decode_statistics(child, mnt_pct_statistics, key_dec, characteristics)
log_maintenance(decoded, cleaning_pct, "Cleaning percent")

# Cleaning count
logging.info("Read cleaning count")
mnt_cnt_statistics = encode_command("2a 00 04 01 00", key_dec)
decoded = read_and_decode_statistics(child, mnt_cnt_statistics, key_dec, characteristics)
decoded = [int("".join(["%02x" % d for d in decoded[i:i+2]]), 16) for i in range(0, len(decoded), 2)]
log_maintenance(decoded, cleaning_count, "Cleaning count")
