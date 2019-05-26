if exists("b:current_syntax")
  finish
endif

syn region scoundrelComment start="\v\(\*" end="\v\*\)"

syn keyword scoundrelKeyword and else elsif end false fn
syn keyword scoundrelKeyword if in let mod or then true
syn match scoundrelKeyword "\v\$"

syn match scoundrelNumber "\v\d"

syn match scoundrelOperator "\v\*"
syn match scoundrelOperator "\v/"
syn match scoundrelOperator "\v\+"
syn match scoundrelOperator "\v-"
syn match scoundrelOperator "\v\:\="
syn match scoundrelOperator "\v\=\="
syn match scoundrelOperator "\v<>"

syn match scoundrelString "\v'.*'"

highlight link scoundrelComment Comment
highlight link scoundrelKeyword Keyword
highlight link scoundrelNumber Number
highlight link scoundrelOperator Operator
highlight link scoundrelString String

let b:current_syntax = "scoundrel"
