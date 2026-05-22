" Vim syntax file
" Language: Phronesis Policy Language
" Maintainer: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
" Latest Revision: 2026-01-30
" SPDX-License-Identifier: MPL-2.0

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword phronesisKeyword POLICY CONST IMPORT IF THEN ELSE AND OR NOT IN
syn keyword phronesisAction ACCEPT REJECT REPORT EXECUTE BLOCK
syn keyword phronesisMetadata PRIORITY EXPIRES CREATED_BY AS
syn keyword phronesisTest TEST SCENARIO GIVEN EXPECT DESCRIBE IT
syn keyword phronesisType TYPE Integer String Boolean Float List Map Route

" Constants
syn keyword phronesisBoolean true false
syn keyword phronesisNull nil null
syn keyword phronesisTime never always

" Comments
syn match phronesisComment "#.*$"
syn region phronesisBlockComment start="##" end="##"

" Strings
syn region phronesisString start='"' end='"' skip='\\"' contains=phronesisEscape,phronesisInterpolation
syn region phronesisSingleString start="'" end="'" skip="\\'"
syn match phronesisEscape contained '\\.'
syn match phronesisInterpolation contained '\${[^}]\+}'

" Numbers
syn match phronesisNumber '\<\d\+\>'
syn match phronesisFloat '\<\d\+\.\d\+\([eE][+-]\?\d\+\)\?\>'
syn match phronesisHex '\<0[xX][0-9a-fA-F]\+\>'

" Operators
syn match phronesisOperator '=='
syn match phronesisOperator '!='
syn match phronesisOperator '>='
syn match phronesisOperator '<='
syn match phronesisOperator '>'
syn match phronesisOperator '<'
syn match phronesisOperator '+'
syn match phronesisOperator '-'
syn match phronesisOperator '\*'
syn match phronesisOperator '/'
syn match phronesisOperator '%'
syn match phronesisOperator '&&'
syn match phronesisOperator '||'
syn match phronesisOperator '!'
syn match phronesisOperator '='
syn match phronesisOperator '\.'
syn match phronesisOperator '?\.'

" Standard Library Functions
syn match phronesisStdlib '\<Std\.\(RPKI\|BGP\|Consensus\|Temporal\)\.[a-zA-Z_][a-zA-Z0-9_]*\>'

" Function Calls
syn match phronesisFunction '\<[a-zA-Z_][a-zA-Z0-9_]*\>\s*(' contains=phronesisFunctionName
syn match phronesisFunctionName '\<[a-zA-Z_][a-zA-Z0-9_]*\>' contained

" Policy Names
syn match phronesisPolicy 'POLICY\s\+\zs[a-zA-Z_][a-zA-Z0-9_]*'

" Metadata Values
syn match phronesisMetadataValue 'PRIORITY:\s*\zs\d\+'
syn match phronesisMetadataValue 'EXPIRES:\s*\zs\w\+'
syn match phronesisMetadataValue 'CREATED_BY:\s*\zs\w\+'

" Highlight Links
hi def link phronesisKeyword Keyword
hi def link phronesisAction Statement
hi def link phronesisMetadata PreProc
hi def link phronesisTest Type
hi def link phronesisType Type
hi def link phronesisBoolean Boolean
hi def link phronesisNull Constant
hi def link phronesisTime Constant
hi def link phronesisComment Comment
hi def link phronesisBlockComment Comment
hi def link phronesisString String
hi def link phronesisSingleString String
hi def link phronesisEscape SpecialChar
hi def link phronesisInterpolation Special
hi def link phronesisNumber Number
hi def link phronesisFloat Float
hi def link phronesisHex Number
hi def link phronesisOperator Operator
hi def link phronesisStdlib Function
hi def link phronesisFunction Function
hi def link phronesisFunctionName Function
hi def link phronesisPolicy Identifier
hi def link phronesisMetadataValue Constant

let b:current_syntax = "phronesis"
