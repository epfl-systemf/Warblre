# Publishing `opam` packages

Currently, only the mechanization is published in the [Rocq opam repository](https://rocq-prover.org/packages). To publish a new version:

1. Create a git tag following the format `v[0-9]+.[0-9]+.[0-9]+`: `git tag v1.2.3`
1. Push the newly created tag: `git push origin v1.2.3`
1. Release the new version by specifying the **tag** and providing your GitHub access token: `OPAM_PUBLISH_GH_TOKEN=xxx ./publish.sh v1.2.3`

The last step will fork the target opam registry, create a new branch with the new release, and open a PR back to the registry from the new branch. All of this will be performed in the name of the access token owner!

## Creating a GitHub access token

1. Go to <https://github.com/settings/tokens/new>
2. Check the top-level checkboxes for:
   - repo
   - workflow
