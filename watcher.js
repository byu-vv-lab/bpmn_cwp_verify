import chokidar from "chokidar";
import { execFile } from "child_process";

const WORKSPACE = "/workspaces/bpmn_cwp_verify";

const watcher = chokidar.watch(`${WORKSPACE}/test/resources`, {
    persistent: true,
    usePolling: true,
    interval: 1000,
});

watcher.on("ready", () => {
    console.log("Watcher ready");
});

watcher.on("all", (event, file) => {
    console.log(event, file);
});

watcher.on("change", debouncedRender);
watcher.on("add", debouncedRender);

const debounceTimers = new Map();

function debouncedRender(file) {
    if (!file.endsWith(".mmd")) {
        return;
    }

    if (debounceTimers.has(file)) {
        clearTimeout(debounceTimers.get(file));
    }

    const timer = setTimeout(() => {
        debounceTimers.delete(file);
        render(file);
    }, 1000);

    debounceTimers.set(file, timer);
}

function render(file) {
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
