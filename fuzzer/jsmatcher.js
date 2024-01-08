// prints a single capture group
function group_to_string (grp) {
    if (grp == null) {
        return "Undefined"
    }
    return grp.toString();
}

// prints the value of each group
function print_array (a) {
    output = "";
    for (var i = 0; i < a.length; i++) {
        output += "#";
        output += i.toString();
        output += ":";
        output += group_to_string(a[i]);
        output += "\n";
    }
    return output;
}

// prints the values of named groups
function print_groups (a) {
    if (a.groups == null) {
	return "None";
    }
    output = "";
    for (name in Object.keys(a.groups)) {
        output += "#";
        output += name.toString();
        output += ":";
        output += group_to_string(a.groups[i]);
        output += "\n";
    }
    return output;
}

// prints the value of the indices array for flag d
function print_index_array (a) {
    if (a.indices == null) {
	return "None";
    }
    output = "";
    for (var i = 0; i < a.indices.length; i++) {
        output += "#";
        output += i.toString();
        output += ":";
        output += "(" + a.indices[i][0].toString() + "," + a.indices[i][1].toString() + ")";
        output += "\n";
    }
    return output;
}

// prints the value of the indices for named groups for flag d
function print_indices_groups (a) {
    if (a.indices == null) {
	return "None";
    }
    if (a.indices.groups == null) {
	return "None";
    }
    output = "";
    for (name in Object.keys(a.indices.groups)) {
        output += "#";
        output += name.toString();
        output += ":";
        output += "(" + a.indices.groups[i][0].toString() + "," + a.indices.groups[i][1].toString() + ")";
        output += "\n";
    }
    return output;
}

// prints an Array Exotic returned by exec, match or matchAll
function print_array_exotic (a) {
    s = "";
    s += "index:" + a.index.toString() + "\n";
    s += "array:" + print_array(a) + "\n";
    s += "groups:" + print_groups(a) + "\n";
    s += "indices_array:" + print_index_array(a) + "\n";
    s += "indices_groups:" + print_indices_groups(a) + "\n";
    return s;
}

// prints the result of the test function - a boolean
function print_test (result) {
    return result.toString();
}

// prints the result of the search function - an integer
function print_search (result) {
    return result.toString();
}

// prints the result of the exec function - an array exotic
function print_exec (result) {
    if (result == null) {
	return "NoMatch\n";
    }
    return (print_array_exotic(result));
}

// printing the result of a match in the same way we printed it in OCaml
function print_match (result, glob) {
    if (result == null) {
        return "NoMatch\n";
    }
    // global result: a list of matches
    if (glob) {
	if (result == null) {
	    return "None";
	}
	output = "";
	for (i = 0; i < result.length; i++) {
            output += "·" + result[i];
            output += "\n";
	}
	return output;
    }
    // non-global result: an exec result
    return (print_exec(result));
}

// prints the result of an iterated matchAll - a list of Array Exotic
function print_matchall (result) {
    output = "";
    for (var i = 0; i < result.length; i++) {
        output += "-" + print_array_exotic (result[i]);
        output += "\n";
    }
    return output;
}

// calling the Irregexp JS regex engine
function matcher () {
    // getting the command line arguments
    const regex = process.argv[2];
    const flags = process.argv[3];
    const lastindex = process.argv[4];
    const string = process.argv[5];
    const frontend_func = process.argv[6];
    // building the regex
    const re = new RegExp(regex,flags);
    re.lastIndex = lastindex;
    // matching the regex
    if (frontend_func == "exec") {
	const result = re.exec(string);
	console.log(print_exec(result));
    }
    if (frontend_func == "search") {
	const result = string.search(re);
	console.log(print_search(result));
    }
    if (frontend_func == "test") {
	const result = re.test(string);
	console.log(print_test(result));
    }
    if (frontend_func == "match") {
	const result = string.match(re);
	const glob = /g/.test(flags); // checking if the g flag is present
	console.log(print_match(result,glob));
    }
    if (frontend_func == "matchAll") {
	const result = Array.from(string.matchAll(re));
	console.log(print_matchall(result));
    }
    return 0;
}

matcher();
