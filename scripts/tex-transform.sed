/^\\documentclass/ {
  s/11pt/10pt/
  a\
  \\usepackage{mathtools}
}

s/^\\usepackage{color}/\\usepackage{xcolor}/

# delete the "XX Good 0 Bad" output
/verbatim/,/verbatim/d

/^\\ottprodline/ {
  # delete "Bind X in Y" annotation
  s/\\textsf{bind}.*\\ottnt{[A-Za-z]*}//g

  # delete "S" meta production
  /\\textsf{S}/s/^.*$/}/g
}

# handles newlines for premises of rules
/\\newcommand{\\ottpremise}/a\
\\newcommand{\\ottpremisecont}[1]{ #1 \\qquad }

/\\ottpremise.*\\qquad/ {
  s/\\qquad//
  s/ottpremise/ottpremisecont/
}

# centering adjustment of array instead of left
/\\newcommand{\\ottdrule}/s/{array}{l}/{array}{c}/g

/\\newenvironment{ottdefnblock}/c \
\\newenvironment{ottdefnblock}[3][] \
{ \\framebox{\\mbox{#2}} \\quad #3 \\\\[2ex] \
  \\begin{equation*} \\setlength{\\jot}{3ex} \\begin{gathered}} \
{\\end{gathered}\\end{equation*}\\\\[5ex]}

/\\newcommand{\\ottdefn[A-Za-z]*}\[1\]/,/\\end{ottdefnblock}/ {
  /^\\ottusedrule/ {
    s/\\ottusedrule{//
    s/}$/ \\\\/
  }
  # adjust line breaks for rules
  /^\\ottdrulemonoXX(kind|var|int|app|lambda|castup)/s/\\\\/\\qquad/
  /^\\ottdrule(s)?sXX(var|lit|star|abs|app|forall{}|forallXXl|castup)/s/\\\\/\\qquad/
  /^\\ottdrule(e)?rXX(beta|castup|castdn)/s/\\\\/\\qquad/
  /^\\ottdruledrXX(app|castdn)/s/\\\\/\\qquad/
  /^\\ottdrule(e)?vXX(kind|num|abs|pi)/s/\\\\/\\qquad/
  /^\\ottdrule(s)?wfXX(nil)/s/\\\\/\\qquad/
}
