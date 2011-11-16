#!/bin/sh
EXCLUDES="-xi doc -xi neatspace -xi .git"
NATDOC="NaturalDocs -i . -o html doc -p doc/project/ $EXCLUDES"
WATCHES="*.d *.nt ast std nehe"
while true
do
	$NATDOC
	inotifywait -r $WATCHES
done
