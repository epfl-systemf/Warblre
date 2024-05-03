//Provides: object_to_array
function object_to_array (a) {
    if (a == null || a == undefined) { return a; }

    var res = [];
    for (var key in a) {
        res.push({first: key, second: a[key]})
    }
    return res;
}

//Provides: array_to_pair
function array_to_pair (p) {
    if (p == null || p == undefined) { return p; }
    return { first: p[0], second: p[1] };
}

// Repacks a match as to get rid of exotic arrays.
//Provides: exec_result_repack
//Requires: array_to_pair,object_to_array
function exec_result_repack (r) {
    if (r == null || r == undefined) { return null; }

    return {
        index: r.index,
        input: r.input,
        groups: r.slice(),
        namedGroups: object_to_array(r.groups),
        indices: r.indices?.slice()?.map(array_to_pair),
        namedIndices: object_to_array(r.indices?.groups)?.map(p => { return { first: p.first, second: array_to_pair(p.second) } }),
    };
}