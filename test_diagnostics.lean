import ShellCheck.Parser.Diagnostics

open ShellCheck.Parser.Diagnostics

#eval do
  IO.println "--- Unicode Detection Tests ---"

  -- Smart quotes (using Unicode code points)
  let smartSingleQuoteLeft := Char.ofNat 0x2018  -- '
  let smartSingleQuoteRight := Char.ofNat 0x2019  -- '
  let smartDoubleQuoteLeft := Char.ofNat 0x201C  -- "
  let smartDoubleQuoteRight := Char.ofNat 0x201D  -- "

  IO.println s!"isSmartQuote U+2018 = {isSmartQuote smartSingleQuoteLeft}"
  IO.println s!"isSmartQuote U+2019 = {isSmartQuote smartSingleQuoteRight}"
  IO.println s!"isSmartQuote U+201C = {isSmartQuote smartDoubleQuoteLeft}"
  IO.println s!"isSmartQuote U+201D = {isSmartQuote smartDoubleQuoteRight}"
  IO.println s!"isSmartQuote '\"' (regular) = {isSmartQuote '\"'}"
  IO.println s!"isSmartQuote '\\'' (regular) = {isSmartQuote '\''}"

  -- Smart dashes
  let enDash := Char.ofNat 0x2013  -- –
  let emDash := Char.ofNat 0x2014  -- —

  IO.println s!"isSmartDash U+2013 (en dash) = {isSmartDash enDash}"
  IO.println s!"isSmartDash U+2014 (em dash) = {isSmartDash emDash}"
  IO.println s!"isSmartDash '-' (regular) = {isSmartDash '-'}"

  -- Non-breaking spaces
  let nbsp := Char.ofNat 0x00A0  -- NO-BREAK SPACE
  IO.println s!"isNonBreakingSpace U+00A0 = {isNonBreakingSpace nbsp}"
  IO.println s!"isNonBreakingSpace ' ' (regular) = {isNonBreakingSpace ' '}"

#eval do
  IO.println "\n--- Find Problematic Unicode ---"
  -- Build test string with smart quotes
  let smartDoubleLeft := Char.ofNat 0x201C
  let smartDoubleRight := Char.ofNat 0x201D
  let test1 := s!"echo {smartDoubleLeft}hello{smartDoubleRight}"
  let problems := findProblematicUnicode test1
  IO.println s!"In '{test1}': found {problems.length} problems"
  for (pos, c, code) in problems do
    IO.println s!"  pos={pos}, char=U+{String.ofList (Nat.toDigits 16 c.toNat)}, code={code}"

#eval do
  IO.println "\n--- BOM and CR Detection ---"
  let bomChar := Char.ofNat 0xFEFF
  let testWithBom := String.singleton bomChar ++ "#!/bin/bash"
  IO.println s!"hasBOM (with BOM) = {hasBOM testWithBom}"
  IO.println s!"hasBOM '#!/bin/bash' = {hasBOM "#!/bin/bash"}"
  IO.println s!"hasCarriageReturn 'foo\\r\\n' = {hasCarriageReturn "foo\r\n"}"
  IO.println s!"hasCarriageReturn 'foo\\n' = {hasCarriageReturn "foo\n"}"

#eval do
  IO.println "\n--- Dialect Features ---"
  let bash := dialectFeatures .bash
  let dash := dialectFeatures .dash
  IO.println s!"bash hasDoubleBracket = {bash.hasDoubleBracket}"
  IO.println s!"bash hasArrays = {bash.hasArrays}"
  IO.println s!"dash hasDoubleBracket = {dash.hasDoubleBracket}"
  IO.println s!"dash hasArrays = {dash.hasArrays}"

#eval do
  IO.println "\n--- Context Descriptions ---"
  IO.println s!"inIfClause: {ParseContext.describe .inIfClause}"
  IO.println s!"inWhileLoop: {ParseContext.describe .inWhileLoop}"
  IO.println s!"inFunction: {ParseContext.describe (.inFunction "myfunc")}"
  IO.println s!"inHereDoc: {ParseContext.describe (.inHereDoc "EOF")}"

#eval do
  IO.println "\n--- Feature Support ---"
  IO.println s!"bash supports '[[': {featureSupported .bash "[["}"
  IO.println s!"dash supports '[[': {featureSupported .dash "[["}"
  IO.println s!"bash supports 'arrays': {featureSupported .bash "arrays"}"
  IO.println s!"sh supports 'process-sub': {featureSupported .sh "process-sub"}"

#eval do
  IO.println "\n--- Error Code Definitions ---"
  IO.println s!"SC1015 (smart quote) = {SC1015}"
  IO.println s!"SC1016 (smart dash) = {SC1016}"
  IO.println s!"SC1017 (carriage return) = {SC1017}"
  IO.println s!"SC1018 (non-breaking space) = {SC1018}"

#eval do
  IO.println "\n--- Suggestion Messages ---"
  IO.println s!"Missing 'fi': {suggestMissingKeyword "fi" (some "done")}"
  IO.println s!"Missing 'done': {suggestMissingKeyword "done" none}"
  let smartQuoteChar := Char.ofNat 0x201C
  IO.println s!"Smart quote fix: {suggestSmartQuoteFix smartQuoteChar}"
