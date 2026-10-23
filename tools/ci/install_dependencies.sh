#!/usr/bin/env bash
# Hosted CI only: avoid refreshing unrelated mirrors when packages already exist.
set -euo pipefail
packages=(cmake build-essential libgmp-dev libmpfr-dev python3 "$@")
missing=()
for package in "${packages[@]}"; do
    if ! dpkg-query -W -f='${Status}' "$package" 2>/dev/null | grep -qx 'install ok installed'; then
        missing+=("$package")
    fi
done
if ((${#missing[@]} == 0)); then
    echo 'Build dependencies already installed.'
    exit 0
fi
. /etc/os-release
[[ "$ID" == ubuntu && "$VERSION_CODENAME" =~ ^[a-z]+$ ]]
sources=$(mktemp)
trap 'rm -f "$sources"' EXIT
# Use Ubuntu's signed archive directly. The hosted runner's mirror+file source
# previously hung for 90 minutes while fetching from azure.archive.ubuntu.com.
printf 'deb [signed-by=/usr/share/keyrings/ubuntu-archive-keyring.gpg] https://archive.ubuntu.com/ubuntu %s main universe\n' \
    "$VERSION_CODENAME" "$VERSION_CODENAME-updates" "$VERSION_CODENAME-security" > "$sources"
options=(-o "Dir::Etc::sourcelist=$sources" -o Dir::Etc::sourceparts=-
         -o Acquire::http::Timeout=20 -o Acquire::https::Timeout=20 -o Acquire::Retries=2
         -o APT::Update::Error-Mode=any -o DPkg::Lock::Timeout=30)
sudo timeout --kill-after=10s 180s apt-get "${options[@]}" update
sudo timeout --kill-after=10s 180s apt-get "${options[@]}" install -y --no-install-recommends "${missing[@]}"
