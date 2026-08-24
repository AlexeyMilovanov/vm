#!/bin/bash
# Restart the sorry pipeline if its driver died; always reap orphaned agents.
ROOT=/home/lesha/hstar-separations-lean
CTRL=$ROOT/pipeline
for f in STOP PAUSE COMPLETE WATCHDOG_OFF; do
  [ -e "$CTRL/$f" ] && exit 0
done
# reap agents whose parent died (ppid=1) but still chew on the work tree
for pid in $(pgrep -f "hstar-sep-work"); do
  ppid=$(ps -o ppid= -p "$pid" 2>/dev/null | tr -d " ")
  if [ "$ppid" = "1" ]; then
    echo "[$(date -u +%FT%TZ)] watchdog: killing orphan $pid" >> "$CTRL/watchdog.log"
    kill "$pid" 2>/dev/null
  fi
done
if pgrep -f "python3 scripts/sorry_pipeline[.]py" > /dev/null; then exit 0; fi
echo "[$(date -u +%FT%TZ)] watchdog: restarting driver" >> "$CTRL/watchdog.log"
cd "$ROOT" || exit 1
nohup setsid nice -n 10 python3 scripts/sorry_pipeline.py \
  >> "$CTRL/driver.nohup.log" 2>&1 < /dev/null &
