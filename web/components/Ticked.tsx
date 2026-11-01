import { Fragment } from "react";

/** Text with the wins ledger's `code` spans rendered as code. */
export function Ticked({ text }: { text: string }) {
  const parts = text.split(/`([^`]+)`/);
  return <>{parts.map((p, i) => (i % 2 ? <code key={i}>{p}</code> : <Fragment key={i}>{p}</Fragment>))}</>;
}
