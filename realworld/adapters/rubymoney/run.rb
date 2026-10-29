# Runs RubyMoney's real Money::Allocation.generate on JSON lines, loaded from a checkout.
#
# Usage: ruby run.rb <RubyMoney checkout> < cases.jsonl > results.jsonl
# Input line:  {"amount": int, "ratios": [int, ...], "scale": int}
#   amount is in cents; when scale > 0 the parts passed to the library are the decimal numbers
#   ratio / 10**scale as Floats (as a caller writing 1.1818583143661 would), otherwise the
#   integer ratios themselves.
# Output line: {"shares": [int, ...]}, or {"shares": null, "failure": "..."} when it raises.
# Money#allocate calls Allocation.generate(fractional, parts, true) unless infinite precision
# is enabled, so this calls generate with whole_amounts = true.
require 'json'
require 'bigdecimal'
require File.join(File.expand_path(ARGV[0]), 'lib/money/money/allocation.rb')

$stdout.sync = false
$stdin.each_line do |line|
  line = line.strip
  next if line.empty?
  c = JSON.parse(line)
  scale = c.fetch('scale', 0)
  parts = scale.positive? ? c['ratios'].map { |r| r.to_f / (10**scale) } : c['ratios']
  out =
    begin
      shares = Money::Allocation.generate(c['amount'], parts, true)
      { 'shares' => shares.map { |x| x.to_i == x ? x.to_i : x.to_f } }
    rescue StandardError => e
      { 'shares' => nil, 'failure' => "#{e.class}: #{e.message}" }
    end
  puts JSON.generate(out)
end
