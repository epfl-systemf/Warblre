function object_to_array (a) {
    if (a == null || a == undefined) { return a; }

    var res = [];
    for (const key in Object.keys(a)) {
        res.push({key: key, value: a[key]})
    }
    return res;
}

//Provides: array_to_pair
function array_to_pair (p) {
    if (p == null || p == undefined) { return p; }
    return { first: p[0], second: p[1] };
}

//Provides: exec_result_repack
//Requires: array_to_pair
function exec_result_repack (r) {
    if (r == null || r == undefined) { return null; }

    var result = {
        index: undefined,
        groups: undefined,
        named_groups: undefined,
        indices: undefined,
        named_indices: undefined,
    };

    result.index = r.index;
    result.groups = r.slice();
    result.indices = r.indices?.slice()?.map(array_to_pair);

    return result;
}