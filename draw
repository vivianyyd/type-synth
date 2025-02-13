#!/bin/sh
# Create dot svg
#dot -Tpng type.dot > type.png

cd results

for file in *.dot; do
  base_name="${file%.dot}"
  dot -Tpng "$file" > "${base_name}.png"

#  # Check if the command was successful
#  if [ $? -eq 0 ]; then
#    echo "Successfully generated ${base_name}.png"
#  else
#    echo "Failed to generate ${base_name}.png"
#  fi
done
