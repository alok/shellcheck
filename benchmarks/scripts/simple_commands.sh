#!/bin/bash
# Simple commands benchmark - tests basic parsing speed

echo "Hello World"
ls -la /tmp
cat /etc/hosts
grep pattern file.txt
sed 's/foo/bar/g' input.txt
awk '{print $1}' data.txt

# Variables
name="John"
age=30
echo "Name: $name, Age: $age"

# Command substitution
current_date=$(date +%Y-%m-%d)
file_count=$(ls | wc -l)

# Arithmetic
result=$((5 + 3 * 2))
((counter++))

# Arrays
arr=(one two three four five)
echo "${arr[0]}"
echo "${arr[@]}"
echo "${#arr[@]}"

# Conditionals
if [ -f /etc/passwd ]; then
    echo "File exists"
elif [ -d /tmp ]; then
    echo "Dir exists"
else
    echo "Nothing"
fi

# Loops
for i in 1 2 3 4 5; do
    echo "Number: $i"
done

for file in *.txt; do
    echo "Processing $file"
done

while read -r line; do
    echo "$line"
done < input.txt

# Functions
my_function() {
    local var="$1"
    echo "Received: $var"
    return 0
}

another_func() {
    echo "No args"
}

# Pipes and redirects
cat file.txt | grep pattern | sort | uniq > output.txt
ls 2>/dev/null
command &>/dev/null

# Here documents
cat << 'EOF'
This is a here document
with multiple lines
EOF

# Case statement
case "$1" in
    start)
        echo "Starting"
        ;;
    stop)
        echo "Stopping"
        ;;
    *)
        echo "Unknown"
        ;;
esac
