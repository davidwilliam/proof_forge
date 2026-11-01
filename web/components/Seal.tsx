/**
 * The Passport seal: the identity's conclusion block (the proof) inside the six kernels that check it, on a
 * flat hexagon like the kernel orbit of the home page. A kernel that accepted the proof is lit; the others
 * stay hollow. Decorative: the status word next to it carries the verdict.
 */
export const SEAL_KERNELS = [0, 1, 2, 3, 4, 5].map((i) => {
  const a = (i * Math.PI) / 3;
  return { x: +(50 + 38 * Math.cos(a)).toFixed(2), y: +(50 + 38 * Math.sin(a)).toFixed(2) };
});

export const SEAL_RING = SEAL_KERNELS.map((k, i) => `${i ? "L" : "M"}${k.x} ${k.y}`).join("") + "Z";

export function Seal({ size = 20, lit = 6, className = "" }: { size?: number; lit?: number; className?: string }) {
  return (
    <svg className={`seal ${className}`} width={size} height={size} viewBox="0 0 100 100" aria-hidden="true" focusable="false">
      <path className="seal-ring" d={SEAL_RING} />
      {SEAL_KERNELS.map((k, i) => (
        <rect key={i} className={i < lit ? "seal-kernel is-lit" : "seal-kernel"} x={k.x - 7} y={k.y - 7} width={14} height={14} rx={1.4} />
      ))}
      <rect className="seal-block" x={38} y={38} width={24} height={24} rx={1.6} />
    </svg>
  );
}
