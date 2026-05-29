# Publishing `opam` packages

Currently, only the mechanization is published in the [Rocq opam repository](https://rocq-prover.org/packages). To publish a new version:

1. Create a git tag following the format `v[0-9]+.[0-9]+.[0-9]+`: `git tag v1.2.3`
2. Push the newly created tag: `git push origin v1.2.3`
3. Go to the "Actions" tab on GitHub
4. Choose the "Publish" workflow
5. Click "Run workflow" from the main branch with the "tag" value set to the newly created tag (v1.2.3)

The last step will fork the target opam registry, create a new branch with the new release, and open a PR back to the registry from the new branch. All of this will be performed in the name of the person that ran the GitHub workflow!
