-- Modified from https://github.com/gleachkr/lean.lua
-- and https://github.com/mcanouil/quarto-external/

local lpeg = require("lpeg")

local commentstart = lpeg.P([[/-]])

local commentend = lpeg.P([[-/]])

-- Delimiters inside Lean tokens are code, not documentation. Raw strings can
-- contain quotes, so match their closing quote with the same number of hashes.
local identifierbyte = lpeg.R("az", "AZ", "09", "\128\255") + lpeg.S("_'!?.")
local rawstring = -lpeg.B(identifierbyte) * lpeg.Cmt(
    lpeg.P("r") * lpeg.C(lpeg.P("#") ^ 0) * lpeg.P('"'),
    function(subject, position, hashes)
        local closing = subject:find('"' .. hashes, position, true)
        if closing then return closing + 1 + #hashes end
        return false
    end)
local quotedstring = lpeg.P('"') *
    (lpeg.P("\\") * lpeg.P(1) + (1 - lpeg.P('"'))) ^ 0 * lpeg.P('"')
local quotedidentifier = lpeg.P("«") * (1 - lpeg.P("»")) ^ 0 * lpeg.P("»")
-- In particular, a quote character ('"') must not begin a string token.
local character = lpeg.P("'") * (lpeg.P("\\") * lpeg.P(1) + lpeg.P(1)) * lpeg.P("'")
local linecomment = lpeg.P("--") * (1 - lpeg.S("\r\n")) ^ 0

-- Lean block comments nest. Preserve the inner delimiters in the Markdown
-- body, rather than mistaking the first inner terminator for the outer one.
local nestedcomment = lpeg.P {
    commentstart * (lpeg.V(1) + (1 - commentstart - commentend)) ^ 0 * commentend
}
local commentbody = (nestedcomment + (1 - commentstart - commentend)) ^ 0
local docmarker = (lpeg.S("!-") * -lpeg.P("/")) ^ -1

-- An interpolated string may contain quoted strings (and further interpolated
-- strings) inside its {...} expressions. Keep the entire token in Lean code.
local interpolatedstring = lpeg.P {
    "string",
    string = lpeg.P('!"') * (lpeg.P("\\") * lpeg.P(1) + lpeg.P("{{") +
        lpeg.V("expression") + (1 - lpeg.S('"{'))) ^ 0 * lpeg.P('"'),
    expression = lpeg.P("{") * (lpeg.V("string") + rawstring + quotedstring +
        quotedidentifier + character + linecomment + nestedcomment +
        lpeg.V("expression") + (1 - lpeg.P("}"))) ^ 0 * lpeg.P("}")
}
local codetoken = rawstring + interpolatedstring + quotedstring +
    quotedidentifier + character + linecomment

local function HandleComment(raw)
    return table.unpack(quarto.utils.string_to_blocks(raw))
end

local function HandleCode(raw)
    if raw:find("^[%s%c]+$") then return -1 end
    
    -- If the block ends with "-/\n" or -/  \n", we strip that whitespace
    --
    -- Whitespace is otherwise preserved
    --
    raw = raw:match("^[ \t]*\n(.*)$") or raw
    
    -- Strip leading and trailing empty lines (including lines with only spaces/tabs)
    raw = raw:gsub("^[ \t]*\n", ""):gsub("\n[ \t]*$", "")
    
    return pandoc.CodeBlock(raw, {class = "lean"})

end

local theGrammar = {
    "output",
    output = lpeg.Ct((lpeg.V "block" + lpeg.V "comment") ^ 0) * -lpeg.P(1),
    comment = commentstart * docmarker * lpeg.C(commentbody) * commentend / HandleComment,
    block = lpeg.C((codetoken + (1 - commentstart)) ^ 1) / HandleCode
}

local G = lpeg.P(theGrammar)

return {
  ['lean-include'] = function (args, kwargs, meta, raw_args, context)
    local url = pandoc.utils.stringify(args[1])
    
    local mt, contents = pandoc.mediabag.fetch(url)
    if not contents then
      quarto.log.error("Could not open file '" .. url .. "'. Please check the URL or path.")
      return pandoc.Null()
    end

    local parsed = lpeg.match(G, contents)
    if not parsed then
      error("Could not parse included Lean file '" .. url .. "': unterminated block comment.")
    end

    local lst = pandoc.Blocks({})
    for i, v in ipairs(parsed) do
      if v ~= -1 then
        lst:insert(v)
      end
    end
    return lst
  end
}
