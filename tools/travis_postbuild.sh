#!/bin/bash

DATEVAL=`date +%Y-%m-%d`
VERSIONVAL=master

# Use tag as version
if [ $TRAVIS_TAG ]; then
  VERSIONVAL=$TRAVIS_TAG
fi

sed -e s%@DATE@%${DATEVAL}% .bintray.in > .bintray.tmp
sed -e s%@VERSION@%${VERSIONVAL}% .bintray.tmp > .bintray.json
