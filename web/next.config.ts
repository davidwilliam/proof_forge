import type { NextConfig } from "next";

// The forge session moved from / to /forge. Links made before the move (/?job=..., /?recording=..., /?task=...)
// still open the session; the query string is carried over.
const legacySession = ["job", "recording", "task"].map((key) => ({
  source: "/",
  has: [{ type: "query" as const, key }],
  destination: "/forge",
  permanent: false,
}));

const config: NextConfig = {
  reactStrictMode: true,
  poweredByHeader: false,
  async redirects() {
    return [...legacySession, { source: "/wins", destination: "/frontier", permanent: false }];
  },
};

export default config;
