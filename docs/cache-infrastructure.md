# Lake artifact cache infrastructure

Where the build cache lives, who owns it, and which knob feeds which workflow.

## Cloudflare account

| | |
|---|---|
| Account | `kim@lean-fro.org` |
| Account ID | `d789bf36d237e0cb313be59b927c82bd` |
| Dashboard | https://dash.cloudflare.com/d789bf36d237e0cb313be59b927c82bd |
| R2 bucket | `tauceti-cache` |
| Registrar | `taucetiproject.org`, bought through Cloudflare Registrar in this same account |

The account ID is not a secret: it is the subdomain of the S3 endpoint below. If the dashboard
link 404s, the login you used is not a member of that account.

The account holds other buckets unrelated to this project. Only `tauceti-cache` is ours.

## Endpoints

Reads are anonymous. Lake's download path issues plain unauthenticated `curl` GETs and has no way
to sign them, so the read host must be public; only uploads use a key.

| Purpose | Value | Used by |
|---|---|---|
| `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | `https://cache.taucetiproject.org/artifacts` | `pr-build.yml` read |
| `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | `https://cache.taucetiproject.org/revisions` | `pr-build.yml` read |
| `LAKE_CACHE_ARTIFACT_ENDPOINT` | `https://d789bf36….r2.cloudflarestorage.com/tauceti-cache/artifacts` | `ci.yml` upload |
| `LAKE_CACHE_REVISION_ENDPOINT` | `https://d789bf36….r2.cloudflarestorage.com/tauceti-cache/revisions` | `ci.yml` upload |
| `LAKE_CACHE_KEY` (secret) | `<ACCESS_KEY_ID>:<SECRET>`, read-write | `ci.yml` upload only |

Lake service names: `tauceti-public` for reads, `tauceti-r2` for uploads. Object keys are
`artifacts/TauCetiProject/TauCeti/<hash>.art`, so the endpoint variables hold only the prefix and
Lake appends the scope.

## Why a custom domain

The read path was on `https://pub-1825e93d….r2.dev`, which Cloudflare documents as rate-limited
and "should only be used for development purposes"
(https://developers.cloudflare.com/r2/buckets/public-buckets/). At roughly 1,200 artifacts per
build across about 730 builds a day, throttling (HTTP 429, Cloudflare error 1015, listed at
https://developers.cloudflare.com/support/troubleshooting/http-status-codes/cloudflare-1xxx-errors/)
was routine and left the local cache holding mappings whose artifacts never arrived. Combined with
https://github.com/leanprover/lean4/issues/14670 that turned successful builds red: 28 of 40
consecutive build failures had no Lean error at all.

`cache.taucetiproject.org` is an R2 custom domain on the bucket and carries no such limit. The
`r2.dev` URL was disabled on 2026-08-04 so nothing can silently fall back to it.

Setting up a custom domain requires the zone to live in the same Cloudflare account as the bucket
(https://developers.cloudflare.com/r2/buckets/public-buckets/#add-your-domain-to-cloudflare).
Attaching only a subdomain while keeping DNS elsewhere needs a Business plan (partial CNAME setup,
https://developers.cloudflare.com/dns/zone-setups/partial-setup/) or Enterprise (subdomain zone,
https://developers.cloudflare.com/dns/zone-setups/subdomain-setup/), which is why the domain was
bought in-account rather than carved out of an existing one.

## Cost

Egress from R2 is free. Reads are Class B operations: 10M per month free, then $0.36 per million
(https://developers.cloudflare.com/r2/pricing/, standard storage, prices read 2026-08-04). At
current volume the project sits near 27M reads per month, so roughly $6 per month beyond the free
tier. A custom domain puts Cloudflare Cache in front of the bucket
(https://developers.cloudflare.com/r2/buckets/public-buckets/#caching), so a cache rule on
`cache.taucetiproject.org` would cut that bill: a request answered at the edge never reaches R2
and so is never billed as a Class B operation.

## Related

- `pr-build.yml` retries a partial fetch and discards the cache rather than handing it to the
  offline sandbox. See the comment at that step for when part of it can be simplified.
- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` exit status was
  unreliable. Ships in v4.34.0, not backported to v4.33.0.
