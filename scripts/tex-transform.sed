/^\\documentclass/a\
\\usepackage{mathtools}

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
\\newcommand{\\ottpremisecont}[1]{ #1 }

/\\ottpremise.*\\qquad/s/ottpremise/ottpremisecont/g

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
}