#!/bin/sh

set -e

if [ $# -ne 1 ] || [ -z "${OPAM_PUBLISH_GH_TOKEN:-}" ]; then
	echo "Usage: $0 <git-tag>"
	echo "Publishes to the Rocq opam repository"
	echo "Requires OPAM_PUBLISH_GH_TOKEN environment variable"
	exit 1
fi

TAG="$1"
VERSION="${TAG#v}"
opam publish \
	--packages-directory=released/packages --repo rocq-prover/opam \
	--tag $TAG -v $VERSION LindenRegex/Warblre
