from typing import Dict
import os
import re

LAMBDA_URL = "https://cxvqggpd6swymxnmahwvgfsina0tiokb.lambda-url.us-east-1.on.aws/"


def parse_command(cmd: str) -> Dict[str, str]:
    regex = re.compile(r"^\s*verify\s+(?P<path>[^\s]+)\s*$")
    match = re.match(regex, cmd)
    if match:
        return match.groupdict()
    else:
        raise Exception("Did not Recognize user input")


def get_file(file_name: str, accepted_files: Dict[str, str]) -> None:
    state_regex = re.compile("state.txt")
    cwp_regex = re.compile(".*cwp.*")
    bpmn_regex = re.compile(".*(bpmn|workflow).*")
    behavior_regex = re.compile(".*behavior.*")

    if re.match(state_regex, file_name):
        assert not accepted_files["state"]
        accepted_files["state"] = file_name
    elif re.match(cwp_regex, file_name):
        assert not accepted_files["cwp"]
        accepted_files["cwp"] = file_name
    elif re.match(bpmn_regex, file_name):
        assert not accepted_files["bpmn"]
        accepted_files["bpmn"] = file_name
    elif re.match(behavior_regex, file_name):
        assert not accepted_files["behavior"]
        accepted_files["behavior"] = file_name


def process_command(parsed_input: Dict[str, str]) -> None:
    accepted_files = {"state": "", "cwp": "", "bpmn": "", "behavior": ""}
    try:
        files = os.listdir(parsed_input["path"])
        for file_name in files:
            get_file(file_name, accepted_files)

        assert "" not in set(accepted_files.values())

    except FileNotFoundError as e:
        print("FILE NOT FOUND ERROR", e)
        return


while True:
    user_cmd = input("> ")
    values = parse_command(user_cmd)
    if values:
        process_command(values)
