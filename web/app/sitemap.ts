import type { MetadataRoute } from "next";
import { SITE_PATHS, SITE_URL } from "@/lib/site";

export default function sitemap(): MetadataRoute.Sitemap {
  return SITE_PATHS.map((p) => ({ url: p === "/" ? SITE_URL : `${SITE_URL}${p}` }));
}
