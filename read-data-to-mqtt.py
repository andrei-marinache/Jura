#!/usr/bin/env python3
import pexpect
import time
import logging
import xml.etree.ElementTree as ET
from pathlib import Path
from zipfile import ZipFile
import json
from paho.mqtt import client as mqtt_client
from bt_encoder import BtEncoder
from jura_encoder import JuraEncoder

# Set up logging
logging.basicConfig(level=logging.DEBUG)

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
DEVICE = "AA:BB:CC:DD:EE:FF" ## Device MAC
jura_mac = DEVICE.replace(":", "").lower()
mqtt_username = ""
mqtt_password = ""
mqtt_host = ""
mqtt_port = 1883

# Initialize encoders
bt_encoder = BtEncoder()
jura_encoder = JuraEncoder()

# Parse XML file and return root and namespace
def parse_xml(file_path):
    tree = ET.parse(file_path)
    root = tree.getroot()
    namespace = {'ns': 'http://www.top-tronic.com'}
    return root, namespace

# Extract product information from XML
def extract_products(root, namespace):
    products = [{'Code': int(product.get('Code'), 16), 'Name': product.get('Name')} for product in root.findall('.//ns:PRODUCT', namespace)]
    products.append({'Code': 0, 'Name': 'Total Drinks'})
    return products

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
    child = pexpect.spawn(f"/usr/bin/gatttool -b {device} -I -t random")
    logging.info(f"Connecting to {device}")

    connected = False
    attempts = 0
    while not connected and attempts < 30:
        child.sendline("connect")
        try:
            child.expect("Connection successful", timeout=5)
            connected = True
            logging.info("Connected!")
        except pexpect.TIMEOUT:
            logging.warning("Connection failed, retrying...")
            time.sleep(10)
            attempts += 1

    if not connected:
        logging.error("Failed to connect after 30 attempts. Exiting...")
        exit(1)

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
    command = key_dec+" "+command
    encoded = bt_encoder.encDecBytes([int(x, 16) for x in command.split()], key_dec)
    return "".join(["%02x" % d for d in encoded])

# Read data until a specific value is ready
def read_data_until_ready(child, uuid, ready_value_index, value):
    hex_values = []
    attempts = 0
    max_attempts = 30  # Maximum number of loops before exiting

    while len(hex_values) < ready_value_index + 1 or hex_values[ready_value_index] == value:
        if attempts >= max_attempts:
            logging.error("Maximum attempts reached. Exiting...")
            sys.exit(1)  # Exit the program with error code 1

        while True:
            try:
                child.sendline(f"char-read-uuid {uuid}")
                child.expect(": ")
                break
            except pexpect.TIMEOUT:
                logging.warning("Read attempt timed out, retrying...")
                time.sleep(5)
        data = child.readline().decode().strip()
        value_part = data.split('value: ')[1].strip()
        hex_values = value_part.split()
        logging.debug(f"Read data while waiting to be ready: {value_part}")
        attempts += 1  # Increment the attempt counter
        time.sleep(1)
    return value_part

# Read and decode statistics data
def read_and_decode_statistics(child, command, key_dec, characteristics):
    child.sendline(f"char-write-req {characteristics['statistics_command'][1]} {command}")
    read_data_until_ready(child, characteristics['read_stat'][0], 1, "e1")
    child.sendline(f"char-read-hnd {characteristics['statistics_data'][1]}")
    child.expect(": ")
    while True:
        try:
            data = child.readline().decode().strip()
            break
        except Exception as e:
            logging.warning(f"Failed to read data: {e}. Retrying...")
            time.sleep(5)
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
def log_statistics(decoded, products, tmp):
    for i, byte in enumerate(decoded):
        product_code = i
        product = next((product for product in products if product['Code'] == product_code), None)
        if product:
            product_name = product['Name']
            if byte == 65535:
                byte = 0
            logging.info(f"Product code: {product_code}, Product name: {product_name}, Byte: {byte}")
            tmp.append({product_name: byte})
    return tmp

# Log maintenance data
def log_maintenance(decoded, maintenance_list, label, tmp):
    for i, count in enumerate(maintenance_list):
        if i < len(decoded):
            logging.info(f"{label}: {count}, Value: {decoded[i]}")
            tmp.append({count: decoded[i]})

# Initialize MQTT client
def init_mqtt_client():
    client = mqtt_client.Client(mqtt_client.CallbackAPIVersion.VERSION2)
    client.username_pw_set(mqtt_username, mqtt_password)
    client.connect(mqtt_host, mqtt_port, 60)
    return client

def publish_sensor(client, sensor_data, sensor_type, sensor_id):
    sensor_json = json.dumps(sensor_data, indent=4)
    mqtt_topic = f"homeassistant/{sensor_type}/0x{jura_mac}/{sensor_id}/config"
    client.publish(mqtt_topic, sensor_json, retain=True)

def create_device_info():
    return {
        "identifiers": ["jura_" + jura_mac],
        "manufacturer": "Jura",
        "model": machine['model'],
        "name": "Jura " + machine['model']
    }

def create_sensor_config(sensor_type, sensor_id, name, value_template, unit_of_measurement="", entity_category=None):
    sensor_id = 'jura_'+machine['model'].replace(' ', '_').replace('(', '').replace(')', '').lower()+ '_'+jura_mac+'_'+sensor_id
    config = {
        "availability_mode": "latest",
        "availability_template": "online",
        "device": device_info,
        "enabled_by_default": True,
        "object_id": sensor_id,
        "state_topic": "jura",
        "unique_id": sensor_id,
        "unit_of_measurement": unit_of_measurement,
        "value_template": value_template,
        "name": name
    }
    if sensor_type == "binary_sensor":
        config["payload_on"] = True
        config["payload_off"] = False

    if entity_category:
        config["entity_category"] = entity_category
    return config

# Main function
def main():
    global machine, device_info

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
    cleaning_percents = extract_maintenance_counters(root, namespace, "@TG:C0")
    logging.debug(cleaning_count)
    logging.debug(cleaning_percents)
    alerts = extract_alerts(root, namespace)
    logging.debug(alerts)

    # Create sensors
    client = init_mqtt_client()
    device_info = create_device_info()

    for product in products:
        product_name = product['Name']
        product_id = ''.join(filter(str.isalnum, product_name)).lower()
        value_template = "{% for item in value_json['Product counters'] %}{% if '"+product_name+"' in item %}{{ item['"+product_name+"'] }}{% endif %}{% endfor %}"
        product_sensor = create_sensor_config("sensor", product_id, product_name, value_template)
        publish_sensor(client, product_sensor, "sensor", product_id)

    for cleaning_cnt in cleaning_count:
        cleaning_cnt_id = ''.join(filter(str.isalnum, cleaning_cnt)).lower() + "_cnt"
        value_template = "{% for item in value_json['Cleaning counts'] %}{% if '"+cleaning_cnt+"' in item %}{{ item['"+cleaning_cnt+"'] }}{% endif %}{% endfor %}"
        cleaning_cnt_sensor = create_sensor_config("sensor", cleaning_cnt_id, f"{cleaning_cnt} Counts", value_template, entity_category="diagnostic")
        publish_sensor(client, cleaning_cnt_sensor, "sensor", cleaning_cnt_id)

    for cleaning_pct in cleaning_percents:
        cleaning_pct_id = ''.join(filter(str.isalnum, cleaning_pct)).lower() + "_pct"
#        value_template = "{% for item in value_json['Maintenance percents'] %}{% if '"+cleaning_pct+"' in item %}{% set value = item['"+cleaning_pct+"'] %}{% if value > 100 %}NA{% else %}{{ value }}{% endif %}{% endif %}{% endfor %}"
        value_template = "{% for item in value_json['Maintenance percents'] %}{% if '"+cleaning_pct+"' in item %}{% set value = item['"+cleaning_pct+"'] %}{% if value > 100 %}None{% else %}{{ value }}{% endif %}{% endif %}{% endfor %}"
        cleaning_pct_sensor = create_sensor_config("sensor", cleaning_pct_id, cleaning_pct, value_template, unit_of_measurement="%", entity_category="diagnostic")
        publish_sensor(client, cleaning_pct_sensor, "sensor", cleaning_pct_id)

    for alert in filter(None, alerts):
        alert_id = ''.join(filter(str.isalnum, alert)).lower()+"_alert"
        value_template = '{% if "'+alert+'" in value_json["alerts"] %}True{% else %}False{%endif%}'
        alert_sensor = create_sensor_config("binary_sensor", alert_id, alert, value_template, entity_category="diagnostic")
        publish_sensor(client, alert_sensor, "binary_sensor", alert_id)

    client.disconnect()

    # Read data from machine

    while True:
        try:
            # Get alerts
            logging.info("Get alerts")
            #value_part = read_data_until_ready(child, characteristics["machine_status"][0], 1, "ef")
            value_part = read_data_until_ready(child, characteristics["machine_status"][0], 5, "81")
            data = [int(x, 16) for x in value_part.split()]
            decoded = bt_encoder.encDecBytes(data, key_dec)
            logging.debug(f"Decoded statistics data: {decoded}")

            # Check for active alerts
            tmp = []
            for i in range((len(decoded) - 1) * 8):
                offset_abs = (i >> 3) + 1
                offset_byte = 7 - (i & 0b111)
                if (decoded[offset_abs] >> offset_byte) & 0b1:
                    logging.info(f"Alert active. Alert bit: {i} - {alerts[i]}")
                    tmp.append(alerts[i])

            mqtt_data = {
                "alerts": tmp  # Assign the list of alert messages to the 'alerts' key
            }

            # Read product counters
            logging.info("Read product count")
            tmp = []
            all_statistics = encode_command("00 01 FF FF", key_dec)
            decoded = read_and_decode_statistics(child, all_statistics, key_dec, characteristics)
            decoded = [int("".join(["%02x" % d for d in decoded[i:i+3]]), 16) for i in range(0, len(decoded), 3)]
            logging.debug(f"Current Statistics: {decoded}")
            # Log product information
            tmp = log_statistics(decoded, products, tmp)
            mqtt_data["Product counters"] = tmp

            # Maintenance percents
            tmp = []
            logging.info("Read maintenance percents")
            mnt_pct_statistics = encode_command("00 08 01 00", key_dec)
            decoded = read_and_decode_statistics(child, mnt_pct_statistics, key_dec, characteristics)
            log_maintenance(decoded, cleaning_percents, "Maintenance percents", tmp)
            mqtt_data["Maintenance percents"] = tmp

            # Cleaning counters
            tmp = []
            logging.info("Read cleaning count")
            mnt_cnt_statistics = encode_command("00 04 01 00", key_dec)
            decoded = read_and_decode_statistics(child, mnt_cnt_statistics, key_dec, characteristics)
            decoded = [int("".join(["%02x" % d for d in decoded[i:i+2]]), 16) for i in range(0, len(decoded), 2)]
            log_maintenance(decoded, cleaning_count, "Cleaning counts", tmp)
            mqtt_data["Cleaning counts"] = tmp

            mqtt_data = json.dumps(mqtt_data, indent=4)
            logging.debug(mqtt_data)


            # Publish state
            mqtt_topic = "jura"
            client = init_mqtt_client()
            client.publish(mqtt_topic, str(mqtt_data), retain=True)
            client.publish('jura/availability', '{"state":"online"}')
            client.disconnect()

            time.sleep(120)
        except Exception as e:
            logging.error(f"An error occurred: {e}")
#            mqtt_topic = "jura"
#            client = init_mqtt_client()
#            client.publish(mqtt_topic, str(mqtt_data), retain=True)
#            client.publish('jura/availability', '{"state":"offline"}')
#            client.disconnect()
            break

if __name__ == "__main__":
    while True:
        main()
