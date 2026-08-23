#!/bin/bash
# Restart the sorry pipeline if its driver died. Cron: every 10 minutes.
ROOT=/home/lesha/hstar-separations-lean
CTRL=$ROOT/pipeline
for f in STOP PAUSE COMPLETE WATCHDOG_OFF; do
  [ -e "$CTRL/$f" ] && exit 0
done
if pgrep -f "sorry_pipeline[.]py" > /dev/null; then exit 0; fi
# kill orphaned agents (ppid=1) still chewing on the work tree
for pid in $(pgrep -f "hstar-sep-work"); do
  ppid=$(ps -o ppid= -p "$pid" 2>/dev/null | tr -d " ")
  [ "$ppid" = "1" ] && kill "$pid" 2>/dev/null
done
echo "[$(date -u +%FT%TZ)] watchdog: restarting driver" >> "$CTRL/watchdog.log"
cd "$ROOT" || exit 1
nohup setsid nice -n 10 python3 scripts/sorry_pipeline.py \
  >> "$CTRL/driver.nohup.log" 2>&1 &
