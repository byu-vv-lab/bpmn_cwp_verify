## Developer Setup

There are two options here: `vscode` _devcontainer_ (preferred) and local using a virtual environment.

### Docker Container

This option requires `docker`, `vscode`, and the vscode _Dev Containers_ extension. The `devcontainer` is defined in the `.devcontainer/devcontainer.json` file that includes _customizations_ to install various `vscode` extensions in the `devcontainer` and a call to install additional packages on the image after creation. The post-create actions are defined in the `.devcontainer/post-create.sh` script. It configures the full development environment so there are no further actions required after the image is created.

Open the directory to use the container: `code -n bpmn_cwp_verify`. The `vscode` _Dev Containers_ extension should automatically recognize the presence of a `devcontainer` and prompt to reopen in the container. If the extension doesn't recognize the container, then open the command pallette and search for `Dev Containers: Reopen in Container`.

If the `pyproject.toml` file is changed to add new dependencies etc, then the container will need to be rebuilt: `Dev Containers: Rebuild container` (slow). It should also be possible to just reinstall the project to get the new dependencies (fast): `pip install --editable ".[dev]"`.

### Local Install

The following assume the terminal is in the root directory of the package.

  1. Create a virtual environment
      * In the root directory: `python3 -m venv .venv`
      * Activate the virtual environment: `source .venv/bin/activate`
  1. Install the package, with `dev` dependencies, in editable mode: `pip install --editable ".[dev]"`.
      * Only if above fails with missing packages:
          * `pip install --upgrade setuptools`
          * `pip install --upgrade build`
  1. Enable `pre-commit`: `pre-commit install`
      * `pre-commit run --all-files` will force the check on all files otherwise it will only check the files in the index (i.e., those that are part if the commit)

  To uninstall the package, `pip uninstall bpmn_cwp_verify`. To deactivate the virtual environment: `deactivate`. The entry point for the CLI is `verify`.

  The package uses `setuptools` and is configured in `pyproject.toml`. If a new dependency is required (added), then please update the `pyproject.toml` file accordingly so that the install brings it down as expected. All of the `pre-commit` hooks are defined in the `.pre-commit-config.yaml`. Please update as needed. It currently uses `ruff` for linting and formatting. It uses `mypy` for static typechecking.

  If using the `mypy` vscode extension, then it is necessary to point the executable path to `.venv/bin/dmypy` for it to work correctly.

## Generating ANTLR Stuff

`antlr4 -o src/bpmncwpverify/ -Dlanguage=Python3 antlr/State.g4 `

## Setting up Lambda layer to use the package

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

## TODO

### Repository organization and entry points

  * Remove the hard coded paths on lines 29 and 30 of `cli/main.py` to take the relative path specified in the command line. Add runtime checks, with appropriate error messages, that all the required files (BPMN, CWP, state, etc.) are present in the supplied directory.
      1. bpmn xml file
      1. cwp xml file
      1. file definind the state
  * ~~Move the `CSVIngest`, `BMPN-Generate`, and `CWP-Generate` into the test directory~~
  * Bring over the tests that make sense and add tests as we refactor code.
  * Add an argument to indicate the output directory. Fail if the directory doesn't exist or it doesn't allow read and write permissions
  * Refactor the `src` directory to use appropriate Python package/module names (all lower-case, short, hypens, underscores are allowed)
  * Move code around so that everything to do with CWP is in cwp and everything to do with BPMN is in BPMN etc.
  * Break the `BMPN.py` into several files for flows, nodes, process, and model.
  * Write type stub files for all packages/modules to remove the `mypy` [import-untyped](https://mypy.readthedocs.io/en/latest/error_code_list.html#code-import-untyped) warnings

### Input Validation for BPMN

Add list of _best practices for BPMN_ as separate TODO items.

  * Every element has a _unique friendly name_ so that all errors are reported using the friendly name
  * Add a proper expression parser from ANTLRv4 for the FEEL language and make sure all expressions parse
  * Clearly label start/end events, activities and gates
  * Model should be symmetrical (if branching occurs, try to keep activities lined up)
  * Model should be going from left to right
  * When you can, use gateways instead of conditional flows
  * If no start event, then no end event
  * Split and join gates should have different symbols
  * XOR gates should be marked with "X"
  * Successful path should be the center path (from start gate to successful end gate)
  * If retry behavior can be avoided, do avoid
  * Each "pool" (different systems) should model one process (excluding subprocess)
  * Long empty rectangle (only with name) => collapsed pool
  * Database symbol => data storage/physical data storage
  * Document symbol => data
  * Avoid excessive use of data symbol/objects
  * Avoid changing symbol size/color
  * Task naming = verb (in infinitive form) + object
  * Subprocess naming = object + verb (nominalized)
  * Event naming = object + verb (past tense) (name the state object is leaving event), event naming should also be specific
  * Data-based exclusive gateways should be labeled with a question
  * If not possible to name gateways with question, describe conditions on the outgoing paths (when they are executed)
  * Pool should have same name as process
  * If pool has +1 lane, then each lane should be named its role name given to them by the organization or system name
  * Capitalize where you would normally capitalize
  * Avoid technical terms
  * Everything should have a unique and relevant ID
  * Error events => Interrupting boundary error event

### Input Validation for CWP

  * Add a proper expression parser from ANTLRv4 for the FEEL language and make sure all expressions parse

### Input Validation for state

### Input Validation for Promela for activities (need to look at this more)
