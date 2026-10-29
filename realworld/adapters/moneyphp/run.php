<?php
// Runs moneyphp/money's real Money::allocate on JSON lines, loaded from a checkout.
//
// Usage: php run.php <moneyphp checkout> < cases.jsonl > results.jsonl
// Input line:  {"amount": int, "ratios": [int, ...]}   (amount in cents)
// Output line: {"shares": [int, ...]}, or {"shares": null, "failure": "..."} when allocate
// throws. Runtime notices and warnings (for example "Undefined offset") are turned into
// exceptions, as frameworks and test runners do; deprecation notices are ignored.
$checkout = rtrim($argv[1], '/');
spl_autoload_register(function ($class) use ($checkout) {
    if (strpos($class, 'Money\\') === 0) {
        $file = $checkout . '/src/' . str_replace('\\', '/', substr($class, 6)) . '.php';
        if (file_exists($file)) {
            require $file;
        }
    }
});
set_error_handler(function ($no, $msg, $file, $line) {
    if ($no & (E_DEPRECATED | E_USER_DEPRECATED | E_STRICT)) {
        return true;
    }
    throw new ErrorException($msg, 0, $no, $file, $line);
});
fwrite(STDERR, 'calculators: bcmath=' . (extension_loaded('bcmath') ? 'yes' : 'no') .
    ' gmp=' . (extension_loaded('gmp') ? 'yes' : 'no') . ' php=' . PHP_VERSION . "\n");
while (($line = fgets(STDIN)) !== false) {
    $line = trim($line);
    if ($line === '') {
        continue;
    }
    $case = json_decode($line, true);
    try {
        $money = new Money\Money((string) $case['amount'], new Money\Currency('USD'));
        $parts = $money->allocate($case['ratios']);
        $shares = [];
        foreach ($parts as $part) {
            $shares[] = (int) $part->getAmount();
        }
        $out = ['shares' => $shares];
    } catch (Throwable $e) {
        $out = ['shares' => null, 'failure' => get_class($e) . ': ' . $e->getMessage()];
    }
    echo json_encode($out), "\n";
}
