#!/usr/bin/env ruby

require "cgi"
require "fileutils"
require "tmpdir"

# SOURCE = "/Users/baonguyenn/Downloads/tieuluan01_05_09_baong.075.docx"
# DESTINATION = "/Users/baonguyenn/Downloads/tieuluan01_05_09_baong.075_equations.docx"

def xml_text(value)
  CGI.unescapeHTML(value)
end

def xml_escape(value)
  CGI.escapeHTML(value)
end

def math_candidate?(text)
  return false if text.match?(/\Ahttps?:\/\//i)
  return false unless text.match?(/\\|[=<>]|[_^&∑√]/)

  without_text = text.gsub(/\\text\{(?:[^{}]|\{[^{}]*\})*\}/, "")
  without_text !~ /[À-ỹ]/
end

def incomplete_formula?(text)
  text.count("{") > text.count("}") ||
    text.scan(/\\begin\{/).length > text.scan(/\\end\{/).length ||
    text.scan(/\\left\b/).length > text.scan(/\\right\b/).length ||
    text.rstrip.match?(/[=+\-]\z/)
end

def continuation_line?(text)
  text.lstrip.match?(/\A(?:=|\+|-|\{|\\left\b|\\right\b|\\begin\b|\\end\b|\\frac\b|\\sum\b|\\\|)/)
end

def text_from_paragraph(paragraph)
  paragraph.scan(/<(?:w|m):t(?:\s[^>]*)?>(.*?)<\/(?:w|m):t>/m).flatten.map { |s| xml_text(s) }.join
end

def math_run_only?(run)
  text = text_from_paragraph(run)
  return false unless math_candidate?(text)

  remainder = run.dup
  remainder.gsub!(/<w:rPr(?:\s[^>]*)?>.*?<\/w:rPr>/m, "")
  remainder.gsub!(/<w:t(?:\s[^>]*)?>.*?<\/w:t>/m, "")
  remainder.gsub!(/<w:r(?:\s[^>]*)?>|<\/w:r>/, "")
  remainder.strip.empty?
end

def math_run(text)
  "<m:r><m:t>#{xml_escape(text)}</m:t></m:r>"
end

def math_run_plain(text)
  "<m:r><m:rPr><m:sty m:val=\"p\"/></m:rPr><m:t xml:space=\"preserve\">#{xml_escape(text)}</m:t></m:r>"
end

def sequence(content)
  "<m:e>#{content}</m:e>"
end

class TexParser
  SYMBOLS = {
    "\\alpha" => "α", "\\beta" => "β", "\\gamma" => "γ", "\\delta" => "δ",
    "\\epsilon" => "ε", "\\varepsilon" => "ε", "\\theta" => "θ", "\\lambda" => "λ",
    "\\mu" => "μ", "\\sigma" => "σ", "\\pi" => "π", "\\phi" => "φ",
    "\\eta" => "η", "\\nabla" => "∇", "\\partial" => "∂", "\\infty" => "∞", "\\cdot" => "·",
    "\\odot" => "⊙", "\\times" => "×", "\\rightarrow" => "→", "\\to" => "→",
    "\\leq" => "≤", "\\le" => "≤", "\\geq" => "≥", "\\ge" => "≥",
    "\\neq" => "≠", "\\ne" => "≠", "\\in" => "∈", "\\notin" => "∉",
    "\\cdots" => "⋯", "\\ldots" => "…", "\\vdots" => "⋮", "\\ddots" => "⋱",
    "\\quad" => " ", "\\qquad" => "  ", "\\," => " ", "\\;" => " ",
    "\\|" => "‖", "\\langle" => "⟨", "\\rangle" => "⟩",
    "\\lceil" => "⌈", "\\rceil" => "⌉", "\\lfloor" => "⌊", "\\rfloor" => "⌋"
  }.freeze

  ROMAN_COMMANDS = %w[arg min max log exp tanh sin cos ReLU softmax].freeze
  ROMAN_WORDS = %w[Accuracy Precision Recall Gini MSE MAE RMSE F1 PPL Score CV ReLU Input Convolution Pooling Flatten Output].freeze

  def initialize(source)
    @tokens = source.scan(/\\\\|\\[A-Za-z]+|\\.|[A-Za-z]+|[0-9]+|[[:space:]]+|./m).flat_map do |token|
      token.match?(/\A[A-Za-z]{2,}\z/) && !ROMAN_WORDS.include?(token) ? token.chars : [token]
    end
    @index = 0
  end

  def parse
    parse_sequence
  end

  private

  def peek
    @tokens[@index]
  end

  def take
    token = peek
    @index += 1 if token
    token
  end

  def group
    if peek == "{"
      take
      content = parse_sequence("}")
      take if peek == "}"
      content
    else
      atom
    end
  end

  def parse_sequence(stop = nil)
    output = +""
    until peek.nil? || peek == stop
      token = peek
      if token.match?(/\A[[:space:]]+\z/)
        take
        next
      end
      break if token == "\\right"

      output << term
    end
    output
  end

  def term
    base = atom
    sub = nil
    sup = nil
    while peek == "_" || peek == "^"
      marker = take
      value = group
      marker == "_" ? sub = value : sup = value
    end
    if base.is_a?(Array) && base[0] == :nary
      operand = +""
      while peek && !["+", "-", "=", ",", ")", "]"].include?(peek) && peek != "\\right"
        if peek.match?(/\A[[:space:]]+\z/)
          take
          next
        end
        operand << term
      end
      return "<m:nary><m:naryPr><m:chr m:val=\"#{base[1]}\"/><m:limLoc m:val=\"undOvr\"/></m:naryPr>" \
             "#{sub ? "<m:sub>#{sub}</m:sub>" : "<m:sub/>"}" \
             "#{sup ? "<m:sup>#{sup}</m:sup>" : "<m:sup/>"}<m:e>#{operand}</m:e></m:nary>"
    end
    if sub && sup
      "<m:sSubSup><m:e>#{base}</m:e><m:sub>#{sub}</m:sub><m:sup>#{sup}</m:sup></m:sSubSup>"
    elsif sub
      "<m:sSub><m:e>#{base}</m:e><m:sub>#{sub}</m:sub></m:sSub>"
    elsif sup
      "<m:sSup><m:e>#{base}</m:e><m:sup>#{sup}</m:sup></m:sSup>"
    else
      base.is_a?(Array) ? base[1] : base
    end
  end

  def atom
    token = take
    return "" unless token
    return parse_sequence("}") if token == "{"
    return "" if token == "}"
    return "<m:r><m:t>⁡</m:t></m:r>" if token == "\\"

    if token.start_with?("\\")
      case token
      when "\\frac"
        numerator = group
        denominator = group
        return "<m:f><m:fPr><m:type m:val=\"bar\"/></m:fPr><m:num>#{numerator}</m:num><m:den>#{denominator}</m:den></m:f>"
      when "\\sqrt"
        return "<m:rad><m:radPr><m:degHide m:val=\"1\"/></m:radPr><m:deg/><m:e>#{group}</m:e></m:rad>"
      when "\\hat", "\\tilde", "\\bar", "\\overline", "\\overrightarrow", "\\overleftarrow", "\\vec"
        glyph = { "\\hat" => "̂", "\\tilde" => "̃", "\\bar" => "¯", "\\overline" => "¯",
                  "\\overrightarrow" => "→", "\\overleftarrow" => "←", "\\vec" => "⃗" }[token]
        return "<m:acc><m:accPr><m:chr m:val=\"#{glyph}\"/></m:accPr><m:e>#{group}</m:e></m:acc>"
      when "\\left"
        left = delimiter(take)
        body = parse_sequence
        take if peek == "\\right"
        right = delimiter(take)
        return "<m:d><m:dPr><m:begChr m:val=\"#{xml_escape(left)}\"/><m:endChr m:val=\"#{xml_escape(right)}\"/></m:dPr><m:e>#{body}</m:e></m:d>"
      when "\\sum"
        return [:nary, "∑"]
      when "\\prod"
        return [:nary, "∏"]
      when "\\text", "\\mathrm", "\\operatorname"
        value = group
        return math_run_plain(value.gsub(/<[^>]+>/, ""))
      when "\\mathbb"
        value = group.gsub(/<[^>]+>/, "")
        mapped = { "R" => "ℝ", "N" => "ℕ", "Z" => "ℤ", "Q" => "ℚ", "C" => "ℂ" }[value] || value
        return math_run(mapped)
      when "\\mathcal"
        value = group.gsub(/<[^>]+>/, "")
        mapped = { "L" => "ℒ", "F" => "ℱ", "P" => "𝒫" }[value] || value
        return math_run(mapped)
      end
      return math_run(SYMBOLS[token]) if SYMBOLS.key?(token)
      return math_run_plain(token.delete_prefix("\\")) if ROMAN_COMMANDS.include?(token.delete_prefix("\\"))
      return math_run(token.delete_prefix("\\"))
    end

    if token == "("
      content = parse_sequence(")")
      take if peek == ")"
      return "<m:d><m:dPr><m:begChr m:val=\"(\"/><m:endChr m:val=\")\"/></m:dPr><m:e>#{content}</m:e></m:d>"
    end
    if token == "["
      content = parse_sequence("]")
      take if peek == "]"
      return "<m:d><m:dPr><m:begChr m:val=\"[\"/><m:endChr m:val=\"]\"/></m:dPr><m:e>#{content}</m:e></m:d>"
    end
    return token == ")" || token == "]" ? math_run(token) : roman_or_math(token)
  end

  def roman_or_math(token)
    ROMAN_WORDS.include?(token) ? math_run_plain(token) : math_run(token)
  end

  def delimiter(token)
    return "" unless token
    return SYMBOLS[token] || token.delete_prefix("\\") if token.start_with?("\\")
    token
  end
end

def matrix_omml(environment, body)
  rows = body.split(/\\\\/).map(&:strip).reject(&:empty?)
  matrix = rows.map do |row|
    cells = row.split("&", -1)
    "<m:mr>#{cells.map { |cell| "<m:e>#{convert_tex(cell.strip)}</m:e>" }.join}</m:mr>"
  end.join
  matrix_xml = "<m:m><m:mPr><m:baseJc m:val=\"center\"/></m:mPr>#{matrix}</m:m>"
  case environment
  when "bmatrix"
    "<m:d><m:dPr><m:begChr m:val=\"[\"/><m:endChr m:val=\"]\"/></m:dPr><m:e>#{matrix_xml}</m:e></m:d>"
  when "pmatrix"
    "<m:d><m:dPr><m:begChr m:val=\"(\"/><m:endChr m:val=\")\"/></m:dPr><m:e>#{matrix_xml}</m:e></m:d>"
  when "cases"
    "<m:d><m:dPr><m:begChr m:val=\"{\"/><m:endChr m:val=\"\"/></m:dPr><m:e>#{matrix_xml}</m:e></m:d>"
  else
    matrix_xml
  end
end

def convert_tex(source)
  source = source.gsub(/\r/, "")
  if (match = source.match(/\\begin\{(bmatrix|pmatrix|matrix|cases)\}(.*?)\\end\{\1\}/m))
    before = source[0...match.begin(0)]
    after = source[match.end(0)..]
    return convert_tex(before) + matrix_omml(match[1], match[2]) + convert_tex(after)
  end
  TexParser.new(source).parse
end

def paragraph_with_equation(paragraph, equation)
  start_tag = paragraph[/\A<w:p(?:\s[^>]*)?>/]
  end_tag = "</w:p>"
  inner = paragraph[start_tag.length...-end_tag.length]
  ppr = inner[/<w:pPr(?:\s[^>]*)?>.*?<\/w:pPr>|<w:pPr\s*\/>/m]
  "#{start_tag}#{ppr}#{equation}#{end_tag}"
end

def text_run(text, properties = "")
  space = text.match?(/\A\s|\s\z/) ? ' xml:space="preserve"' : ""
  "<w:r>#{properties}<w:t#{space}>#{xml_escape(text)}</w:t></w:r>"
end

def convert_inline_runs(paragraph)
  paragraph.gsub(/<w:r(?:\s[^>]*)?>.*?<\/w:r>/m) do |run|
    next run unless math_run_only?(run)

    text = text_from_paragraph(run)
    suffix = text[/[.,;:!?]+\z/] || ""
    formula = suffix.empty? ? text : text[0...-suffix.length]
    next run unless math_candidate?(formula) && !formula.empty?

    properties = run[/<w:rPr(?:\s[^>]*)?>.*?<\/w:rPr>/m] || ""
    result = "<m:oMath>#{convert_tex(formula)}</m:oMath>"
    result += text_run(suffix, properties) unless suffix.empty?
    result
  end
end

abort "Source document not found: #{SOURCE}" unless File.file?(SOURCE)
abort "Destination already exists: #{DESTINATION}" if File.exist?(DESTINATION)

original_xml = IO.popen(["unzip", "-p", SOURCE, "word/document.xml"], &:read)
abort "Could not read word/document.xml" unless $?.success? && !original_xml.empty?

paragraph_regex = /<w:p(?:\s[^>]*)?>.*?<\/w:p>/m
paragraphs = []
original_xml.to_enum(:scan, paragraph_regex).each do
  match = Regexp.last_match
  paragraph = match[0]
  paragraph_body = paragraph.sub(/\A<w:p(?:\s[^>]*)?>/m, "").sub(/<\/w:p>\z/m, "")
  paragraph_body_without_properties = paragraph_body.sub(/<w:pPr(?:\s[^>]*)?>.*?<\/w:pPr>|<w:pPr\s*\/>/m, "")
  paragraphs << {
    start: match.begin(0),
    finish: match.end(0),
    xml: paragraph,
    text: text_from_paragraph(paragraph),
    existing_math: paragraph.include?("<m:oMath"),
    blank: text_from_paragraph(paragraph).empty? &&
      !paragraph_body_without_properties.match?(/<w:(?:drawing|object|hyperlink|bookmarkStart|fldChar)|<m:oMath/)
  }
end

converted_count = 0
output = +""
cursor = 0
index = 0
while index < paragraphs.length
  paragraph = paragraphs[index]
  if math_candidate?(paragraph[:text])
    last = index
    latex_parts = [paragraph[:text]]
    while last + 1 < paragraphs.length
      following_index = last + 1
      while following_index < paragraphs.length && paragraphs[following_index][:blank] &&
            incomplete_formula?(latex_parts.join("\n"))
        blank_paragraph = paragraphs[following_index]
        previous = paragraphs[following_index - 1]
        break unless original_xml[previous[:finish]...blank_paragraph[:start]].match?(/\A\s*\z/)
        following_index += 1
      end
      break if following_index >= paragraphs.length

      following = paragraphs[following_index]
      bridge_is_blank = (last + 1...following_index).all? do |blank_index|
        previous = paragraphs[blank_index - 1]
        blank_paragraph = paragraphs[blank_index]
        original_xml[previous[:finish]...blank_paragraph[:start]].match?(/\A\s*\z/)
      end
      previous = paragraphs[following_index - 1]
      bridge_is_blank &&= original_xml[previous[:finish]...following[:start]].match?(/\A\s*\z/)
      separator = original_xml[paragraphs[last][:finish]...following[:start]]
      break unless math_candidate?(following[:text]) &&
                   (bridge_is_blank || separator.match?(/\A\s*\z/))
      duplicate_existing_equation = following[:existing_math] && (latex_parts + [following[:text]]).uniq.length == 1
      break unless duplicate_existing_equation || incomplete_formula?(latex_parts.join("\n")) ||
                   continuation_line?(following[:text])
      latex_parts << following[:text]
      last = following_index
    end

    output << original_xml[cursor...paragraph[:start]]
    block = paragraphs[index..last]
    existing_math = block.reverse.find { |entry| entry[:existing_math] }
    render_paragraph = existing_math || paragraph
    latex = if existing_math
      block.map { |entry| entry[:text] }.uniq.join("\n")
    else
      latex_parts.join("\n")
    end
    output << paragraph_with_equation(render_paragraph[:xml], "<m:oMath>#{convert_tex(latex)}</m:oMath>")
    cursor = paragraphs[last][:finish]
    converted_count += 1
    index = last + 1
  else
    output << original_xml[cursor...paragraph[:start]]
    transformed = convert_inline_runs(paragraph[:xml])
    if transformed != paragraph[:xml]
      converted_count += transformed.scan("<m:oMath>").length
    end
    output << transformed
    cursor = paragraph[:finish]
    index += 1
  end
end
output << original_xml[cursor..]

Dir.mktmpdir("docx-equations") do |directory|
  xml_path = File.join(directory, "word", "document.xml")
  FileUtils.mkdir_p(File.dirname(xml_path))
  File.binwrite(xml_path, output)
  FileUtils.cp(SOURCE, DESTINATION)
  system("zip", "-q", DESTINATION, "word/document.xml", chdir: directory) ||
    abort("Failed to update the output DOCX archive")
end

puts "Created #{DESTINATION}"
puts "Converted formula paragraphs or inline equations: #{converted_count}"
puts "Remaining raw LaTeX command runs: #{output.scan(/<(?:w|m):t[^>]*>[^<]*\\\\[A-Za-z]+/).length}"
