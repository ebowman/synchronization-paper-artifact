#!/bin/bash
# Build the Scala.js web application
# Run from the simulation/ directory
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

echo "Building Scala.js (full optimization)..."
sbt prioritizerJS/fullLinkJS

echo "Copying to docs/..."
# Use the most recently modified output to handle multiple Scala versions
JS_FILE=$(ls -t js/target/scala-*/prioritizer-opt/main.js | head -1)
cp "$JS_FILE" ../docs/prioritizer-opt.js

echo "Done. Open docs/index.html in a browser or serve with:"
echo "  cd ../docs && python3 -m http.server 8080"
