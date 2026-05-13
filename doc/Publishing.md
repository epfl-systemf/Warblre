# Publishing `opam` packages

Currently, only the mechanization is published in the [Rocq opam repository](https://rocq-prover.org/packages). To publish a new version:

1. Create a git tag following the format `v[0-9]+.[0-9]+.[0-9]+`: `git tag v1.2.3`

> [!IMPORTANT]
> Follow [semantic versioning](https://semver.org)!

2. Push the newly created tag: `git push origin v1.2.3`
3. The CD will publish a request for a new release

The last step will fork the target opam registry, create a new branch with the new release, and open a PR back to the registry from the new branch. All of this will be performed in the name of git tag pusher!
