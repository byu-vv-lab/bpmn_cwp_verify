import json
from typing import Any

from returns.io import IOResult
from returns.pipeline import is_successful
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.cli import web_verify
from bpmncwpverify.core.error import Error
from bpmncwpverify.core.spin import SpinVerificationReport


def lambda_handler(event: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    try:
        body = json.loads(event["body"])
        files = body.get("files", [])
        if not files:
            return {
                "statusCode": 400,
                "body": json.dumps({"error": "No files received"}),
            }
        bpmnData = files[0]
        cwpData = files[1]
        stateData = files[2]

        result: IOResult[SpinVerificationReport, Error] = web_verify(
            stateData, cwpData, bpmnData
        )
        if is_successful(result):
            outputs: SpinVerificationReport = unsafe_perform_io(result.unwrap())
            return {
                "statusCode": 200,
                "body": json.dumps(
                    {
                        "file_path": outputs.file_path,
                        "promela": outputs.promela,
                        "spin_cli_args": outputs.spin_cli_args,
                        "spin_report": outputs.spin_report,
                    }
                ),
            }
        else:
            return {
                "statusCode": 400,
                "body": json.dumps({"error": "Verification failed"}),
            }
    except Exception as e:
        return {"statusCode": 500, "body": json.dumps({"error": str(e)})}
