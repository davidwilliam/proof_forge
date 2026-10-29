// Runs Spliit's real getBalances on JSON lines, compiled unmodified from a checkout.
//
// Usage: node run.cjs <spliit checkout>  < cases.jsonl  > results.jsonl
// Input line:  {"amount": int, "ratios": [int, ...]}   (one expense, amount in cents)
// Output line: {"shares": [int, ...]} with each participant's paidFor balance, in ratio order,
//              or {"shares": null, "failure": "..."} if getBalances throws.
// The expense is paid by a separate participant. All ratios equal to 1 use split mode EVENLY,
// any other ratios use BY_SHARES with the ratios as shares. Only src/lib/*.ts files are
// loaded; TypeScript is transpiled with `transpileModule` and `@/` resolves to src/.
const fs = require('fs')
const path = require('path')
const Module = require('module')
const readline = require('readline')
const ts = require('typescript')

const checkout = path.resolve(process.argv[2])
require.extensions['.ts'] = function (module, filename) {
  const out = ts.transpileModule(fs.readFileSync(filename, 'utf8'), {
    fileName: filename,
    compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2020, esModuleInterop: true },
  })
  module._compile(out.outputText, filename)
}
const resolve = Module._resolveFilename
Module._resolveFilename = function (request, parent, ...rest) {
  if (request.startsWith('@/')) request = path.join(checkout, 'src', request.slice(2))
  return resolve.call(this, request, parent, ...rest)
}
const { getBalances } = require(path.join(checkout, 'src/lib/balances.ts'))

const pid = (i) => 'p' + String(i).padStart(3, '0')
const rl = readline.createInterface({ input: process.stdin })
rl.on('line', (line) => {
  if (!line.trim()) return
  const { amount, ratios } = JSON.parse(line)
  const even = ratios.every((r) => r === 1)
  const expense = {
    id: 'expense-1',
    amount,
    splitMode: even ? 'EVENLY' : 'BY_SHARES',
    paidBy: { id: 'payer' },
    paidFor: ratios.map((shares, i) => ({ participant: { id: pid(i) }, shares })),
  }
  let out
  try {
    const balances = getBalances([expense])
    out = { shares: ratios.map((_, i) => (balances[pid(i)] ? balances[pid(i)].paidFor : null)) }
    if (out.shares.some((x) => x === null || !Number.isFinite(x))) out = { shares: null, failure: 'missing or non-finite share' }
  } catch (e) {
    out = { shares: null, failure: String(e && e.message ? e.message : e) }
  }
  process.stdout.write(JSON.stringify(out) + '\n')
})
