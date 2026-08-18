import chokidar from "chokidar";
import { execFile } from "child_process";

const WORKSPACE = "/workspaces/bpmn_cwp_verify";

const watcher = chokidar.watch(`${WORKSPACE}/test/resources`, {
    persistent: true,
    usePolling: true,
    interval: 100,
});

watcher.on("ready", () => {
    console.log("Watcher ready");
});

watcher.on("all", (event, file) => {
    console.log(event, file);
});

watcher.on("change", render);
watcher.on("add", render);

function render(file) {
    if (!file.endsWith(".mmd")) {
        return;
    }

    const output = file.replace(/\.mmd$/, ".svg");

    console.log(`Rendering ${file} → ${output}`);

    execFile("npx", [
        "mmdc",
        "-p", `${WORKSPACE}/puppeteer-config.json`,
        "-i", file,
        "-o", output
    ], (error) => {
        if (error) {
            console.error(`Failed to render ${file}:`, error);
            return;
        }

        console.log(`Rendered ${file} → ${output}`);
    });
}
