/** The four steps a repair goes through before it counts. Shared by the home page and the forge session. */
export function Pipeline({ className = "" }: { className?: string }) {
  return (
    <ol className={`pipeline ${className}`.trim()} aria-label="How a repair counts">
      <li>
        <strong>Lock</strong>
        The owner&apos;s requirements, hashed.
      </li>
      <li>
        <strong>Repair</strong>
        A Muse model fixes the code and proves each one.
      </li>
      <li>
        <strong>Check</strong>
        Fresh Comparator, kernel replay and property tests.
      </li>
      <li>
        <strong>Passport</strong>
        Statuses come only from that check.
      </li>
    </ol>
  );
}
