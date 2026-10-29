// Runs go-money's real Money.Split on JSON lines; the module is replaced by a checkout.
//
// Input line:  {"amount": int, "n": int}   (amount in cents)
// Output line: {"shares": [int, ...]}, or {"shares": null, "failure": "..."} when Split returns
// an error or panics (the panic is recovered and reported).
package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"

	money "github.com/Rhymond/go-money"
)

type input struct {
	Amount int64 `json:"amount"`
	N      int   `json:"n"`
}

type output struct {
	Shares  []int64 `json:"shares"`
	Failure string  `json:"failure,omitempty"`
}

func split(amount int64, n int) (out output) {
	defer func() {
		if r := recover(); r != nil {
			out = output{Shares: nil, Failure: fmt.Sprint("panic: ", r)}
		}
	}()
	parts, err := money.New(amount, "USD").Split(n)
	if err != nil {
		return output{Shares: nil, Failure: "error: " + err.Error()}
	}
	shares := make([]int64, 0, len(parts))
	for _, p := range parts {
		shares = append(shares, p.Amount())
	}
	return output{Shares: shares}
}

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	for in.Scan() {
		var c input
		if err := json.Unmarshal(in.Bytes(), &c); err != nil {
			continue
		}
		b, _ := json.Marshal(split(c.Amount, c.N))
		w.Write(append(b, '\n'))
	}
}
