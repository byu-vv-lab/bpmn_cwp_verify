## Current Lambda Code
```
import json
import os
import sys
from bpmncwpverify.cli import web_verify
from returns.pipeline import is_successful
from returns.result import Result

def lambda_handler(event, context):
    try:
        body = json.loads(event["body"])
        files = body.get("files", [])
        if not files:
            return {
                "statusCode": 400,
                "body": json.dumps({"error": "No files received"})
            }
        bpmnData = files[0]
        cwpData = files[1]
        stateData = files[2]
        behaviorData = files[3]

        result : Result = web_verify(bpmnData, cwpData, stateData, behaviorData)
        if is_successful(result):
            outputs = result.unwrap()
            return {
                "statusCode": 200,
                "body": json.dumps({"message": outputs.promela})
            }
        else:
            return {
                "statusCode": 400,
                "body": json.dumps({"error": "Verification failed"})
            }
    except Exception as e:
        return {
            "statusCode": 500,
            "body": json.dumps({"error": str(e)})
        }
```

## Deploying as a Lambda to AWS

The following are steps on how to set up your lambda function so that it can use this package as a dependency

  1. Make sure that the `build` package is installed in the python environment you have created for `bpmn_cwp_verify`
      * This can be done by simply using the command `pip install build`
  1. Use the command `python -m build`. Once the command is executed, you should see a new directory named `dist`. Inside this new directory there should be several new files. The one you want to pay attentio to is the one that ends with the file extension `.whl`
  1. Now either in a terminal or your file explorer create a new directory with this specific directory structure `[any name] -> python -> lib -> [python version] -> site-packages`
      * The top layer directory can be named anything as long as it is not in the `bpmn_cwp_verify` directory. The subdirectory of `lib` should be the python version being used in the lambda function. At this moment, we are using a runtime of Python 3.12 so the directory should be named `python3.12`
  1. In a python environment, run the command `pip install --upgrade [path to .whl file] -t [path to site-packages directory]`
  1. Then zip everything from `python` and below (so excluding the parent directory)
  1. Once the file content is zipped, go to your AWS console and search up Lambda and click on the top result
  1. Navigate to where it says `Layers`
  1. If you already have a custom made layer, simply click on the custom layer and click on `Create Version`. If this is the first time creating a layer, simply click on `Create Layer`
  1. Upload the zip file and select the runtime. Allow it some time to upload after clicking on `Create`
  1. Once it is finished creating, navigate to the `Functions` tab of the Lambda console
  1. Click on the function and scroll down to where it is titled `Layers`
  1. If you already added the layer before, simply click on `Edit` then click on the drop down menu underneath the `Layer Version` section of the table and select the desired version. If you have not added the layer yet to the function, click on `Add layer` then select `Custom layers` from the different options it provides. Then your custom layer should appear from the dropdown menu. Select the layer. Your function is now ready to use the `bpmn_cwp_verify` package
