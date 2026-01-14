{-# LANGUAGE OverloadedStrings #-}

import Text.Pandoc
import Text.Pandoc.Writers.Markdown
import Text.Pandoc.Error
import qualified Data.Text as T

-- Example 1: Convert Markdown to Pandoc's internal representation
markdownToPandoc :: T.Text -> Pandoc
markdownToPandoc = either (error "Invalid Markdown") id . runPure . readMarkdown def

-- Example 2: Convert Pandoc to HTML
pandocToHtml :: Pandoc -> T.Text
pandocToHtml = writeHtml def

-- Example 3: Convert Markdown string to HTML
markdownToHtml :: T.Text -> T.Text
markdownToHtml md = pandocToHtml (markdownToPandoc md)

-- Example 4: Read a Markdown file and convert it to HTML
{-
 - markdownFileToHtml :: FilePath -> IO T.Text
markdownFileToHtml path = do
    md <- T.readFile path
    return (markdownToHtml md)
-}
-- Example 5: Convert a list of strings to a Pandoc unordered list
stringsToList :: [T.Text] -> Pandoc
stringsToList items = Plain (map (Plain . Str) items)

-- Example 6: Convert a list of strings to HTML unordered list
listToHtml :: [T.Text] -> T.Text
listToHtml items = writeHtml def (stringsToList items)

-- Example 7: Create a header in Pandoc
headerExample :: Pandoc
headerExample = Pandoc nullMeta [Header 1 nullAttr [Str "Hello World"]]

-- Example 8: Convert a header to HTML
headerToHtml :: T.Text
headerToHtml = writeHtml def headerExample

-- Example 9: Create a simple document with a header and a paragraph
simpleDoc :: Pandoc
simpleDoc = Pandoc nullMeta [Header 1 nullAttr [Str "Welcome"], Plain [Str "This is a simple document."]]

-- Example 10: Convert the simple document to HTML
simpleDocToHtml :: T.Text
simpleDocToHtml = writeHtml def simpleDoc

-- 1. Convert plain text to Pandoc
plainTextToPandoc :: Pandoc
plainTextToPandoc = Pandoc nullMeta ["Hello, World!"] []

-- 2. Convert a Markdown string to Pandoc
markdownToPandoc1 :: Pandoc
markdownToPandoc1 = readMarkdown def "# Header"

-- 3. Convert Pandoc to Markdown
pandocToMarkdown :: String
pandocToMarkdown = writeMarkdown def (Pandoc nullMeta ["Hello, World!"] [])

-- 4. Create a simple document with a paragraph
simpleDoc1 :: Pandoc
simpleDoc1 = Pandoc nullMeta [Plain [Str "This is a simple document."]]

-- 5. Create a document with a header and a paragraph
headerAndParagraph :: Pandoc
headerAndParagraph = Pandoc nullMeta [Header 1 ("Header", [], []) , Plain [Str "This is a paragraph."]]

-- 6. Create a document with multiple paragraphs
multiParagraphs :: Pandoc
multiParagraphs = Pandoc nullMeta
  [ Plain [Str "First paragraph."]
  , Plain [Str "Second paragraph."]
  ]

-- 7. Create a list of items
unorderedList :: Pandoc
unorderedList = Pandoc nullMeta [BulletList [[Plain [Str "Item 1"]], [Plain [Str "Item 2"]]]]

-- 8. Create a numbered list
orderedList :: Pandoc
orderedList = Pandoc nullMeta [OrderedList 1 [[Plain [Str "First item"]], [Plain [Str "Second item"]]]]

-- 9. Create a blockquote
blockquote :: Pandoc
blockquote = Pandoc nullMeta [BlockQuote [Plain [Str "This is a quote."]]]

-- 10. Create a code block
codeBlock :: Pandoc
codeBlock = Pandoc nullMeta [CodeBlock (Ident "code" ["lang-haskell"]) "main = putStrLn \"Hello, World!\""]

-- 11. Create a table
simpleTable :: Pandoc
simpleTable = Pandoc nullMeta [Table Nothing ["Header 1", "Header 2"] [AlignDefault, AlignDefault] [[Plain [Str "Row 1, Col 1"], Plain [Str "Row 1, Col 2"]]]]

-- 12. Convert HTML to Pandoc
htmlToPandoc :: Pandoc
htmlToPandoc = readHtml def "<p>Hello, HTML!</p>"

-- 13. Convert a Pandoc document to HTML
pandocToHtml1 :: String
pandocToHtml1 = writeHtml def (Pandoc nullMeta [Plain [Str "Hello, HTML!"]])

-- 14. Create an image
image :: Pandoc
image = Pandoc nullMeta [Image nullMeta (Str "Alt text") "image.png"]

-- 15. Define an inline code
inlineCode :: Pandoc
inlineCode = Pandoc nullMeta [Plain [Space, Code (Ident "code") "code snippet", Space]]

-- 16. Create emphasis text
emphasisText :: Pandoc
emphasisText = Pandoc nullMeta [Plain [Emph [Str "Emphasized text."]]]

-- 17. Create strong text
strongText :: Pandoc
strongText = Pandoc nullMeta [Plain [Strong [Str "Strong text."]]]

-- 18. Create a link
link :: Pandoc
link = Pandoc nullMeta [Plain [Link [Str "Haskell" ] "http://haskell.org" "Haskell link"]]

-- 19. Create a footnote
footnote :: Pandoc
footnote = Pandoc nullMeta [Plain [Str "Here is a footnote reference."], Footnote ("fn1", [], []) [Plain [Str "This is a footnote."]]]

-- 20. Adding metadata
metaDoc :: Pandoc
metaDoc = Pandoc (Meta [(MetaString "title", "My Document")]) [Plain [Str "Document with metadata."]]

-- 21. Create a horizontal rule
horizontalRule :: Pandoc
horizontalRule = Pandoc nullMeta [HorizontalRule]

-- 22. Create a definition list
definitionList :: Pandoc
definitionList = Pandoc nullMeta [DefList [[Plain [Str "term"], Plain [Str "definition"]]]]

-- 23. Create a simple note
note :: Pandoc
note = Pandoc nullMeta [Note [Plain [Str "This is a note."]]]

-- 24. Create a title block
titleBlock :: Pandoc
titleBlock = Pandoc nullMeta [Header 1 ("Title", [], [])]

-- 25. Combine elements in a single document
combinedDoc :: Pandoc
combinedDoc = Pandoc nullMeta
  [ Header 1 ("Main Title", [], [])
  , Plain [Str "Some introduction text."]
  , BulletList [[Plain [Str "First point"]], [Plain [Str "Second point"]]]
  ]

-- 26. Create a preformatted text
preformatted :: Pandoc
preformatted = Pandoc nullMeta [Plain [Str "This is preformatted text."]]

-- 27. Create a nested list
nestedList :: Pandoc
nestedList = Pandoc nullMeta
  [ BulletList
    [[Plain [Str "Main Item 1"], BulletList [[Plain [Str "Sub Item 1"]]]],
     [Plain [Str "Main Item 2"]]]
  ]

-- 28. Create a custom block with formatted text
customBlock :: Pandoc
customBlock = Pandoc nullMeta [Plain [Str "This is a custom block."]]

-- 29. Add a source code section
sourceCode :: Pandoc
sourceCode = Pandoc nullMeta [CodeBlock (Ident "hs" ["haskell"]) "let x = 5"]

-- 30. Create a paragraph with inline elements
inlineElements :: Pandoc
inlineElements = Pandoc nullMeta [Plain [Str "Using ", Emph [Str "inline"], Str " elements."]]

--- 1. runPure
--- 2. readMarkdown
--- 3. writeMarkdown
--- 4. readLaTeX
--- 5. writeLaTeX
--- 6. readHTML
--- 7. writeHTML
--- 8. readRST
--- 9. writeRST
--- 10. readOrg
--- 11. writeOrg
--- 12. readText
--- 13. writeText
--- 14. readDocx
--- 15. writeDocx
--- 16. readEPUB
--- 17. writeEPUB
--- 18. readODT
--- 19. writeODT
--- 20. readMediaWiki
--- 21. writeMediaWiki
--- 22. readCSV
--- 23. writeCSV
--- 24. readJSON
--- 25. writeJSON
--- 26. readConfluence
--- 27. writeConfluence
--- 28. readGitHubMarkdown
--- 29. writeGitHubMarkdown
--- 30. runConvert
--- 31. readPandoc
--- 32. writePandoc
--- 33. setOptions
--- 34. addAttribute
--- 35. inlineCode
--- 36. blockQuote
--- 37. emph
--- 38. strong
--- 39. hyperlink
--- 40. list
--- 41. table
--- 42. header
--- 43. plain
--- 44. rawBlock
--- 45. rawInline
--- 46. joinBlocks
--- 47. extractMeta
--- 48. setMeta
--- 49. applyReaderOptions
--- 50. applyWriterOptions
---
