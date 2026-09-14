#!/bin/sh
# Fetch the challenge instances from raveltech.io.
# The small solution files are kept in solutions/.
set -e
base="https://raveltech.io/challenges"
cd "$(dirname "$0")"
for f in chal_s7_n2 chal_s11_n5 chal_semi_direct_s7_n2 \
         chal_semi_direct_s11_n5 chal_semi_direct_s11_n5_variant; do
    echo "fetching $f.json.gz ..."
    curl -fL -o "$f.json.gz" "$base/$f.json.gz"
done
echo "done."
