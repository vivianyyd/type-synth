#!/bin/bash


# Extract the _cons function using awk
awk '
/^void[ \t]+_cons[ \t]*\(/ { in_func=1 }
/^\/\/ FUNCTION END/ && in_func { print; exit }
in_func { print }
'
