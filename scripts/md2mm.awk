#!/usr/bin/env -S awk -f
# Convert Markdown to Metamath (headings, etc.)

BEGIN {
    heading = "^#+[[:space:]]+"

    marker[1] = "##"
    marker[2] = "#*"
    marker[3] = "=-"
    marker[4] = "-."
}

$0 ~ heading {
    match($0, /^#+/)
    level = RLENGTH

    title = $0
    sub(heading, "", title)

    print("$(")
    marker_line(level)
    printf("  %s\n", title)
    marker_line(level)
    print("$)")

    next
}

{ print }

function marker_line(level) {
    for (i = 1; i <= 39; i++) printf("%s", marker[level]) # 78 characters
	printf("%c\n", substr(marker[level], 1, 1)) # +1 character
}
