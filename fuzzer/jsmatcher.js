// Print a single capture group
function group_to_string (grp) {
    if (grp == null || grp == undefined) {
        return "Undefined"
    }
    return "'" + grp.toString() + "'";
}

// Print a single range
function range_to_string (range) {
    if (range == null || range == undefined) {
        return "Undefined"
    }
    return "(" + range[0].toString() + "," + range[1].toString() + ")"
}

// a: array to print; pk: index printer; pv: value printer; none: result if a is none/undefined
function print_array (a, pk, pv, none) {
    if (a == null || a == undefined) { return none; }

    const strs = a.map((e, i) => {
        var output = "\t# ";
        output += pk(i);
        output += " : ";
        output += pv(e);
        return output;
    });
    return strs.join("\n");
}

// a: object to print; pv: value printer; none: result if a is none/undefined
function print_object (a, pv, none) {
    if (a == null || a == undefined) { return none; }

    const strs = Object.keys(a).map(k => {
        var output = "\t# ";
        output += k;
        output += " : ";
        output += pv(a[k]);
        return output;
    });
    return strs.join("\n");
}

// Print an Array Exotic returned by exec, match or matchAll
function print_array_exotic (a) {
    s = "";
    s += "Start: " + a.index.toString() + "\n";
    s += "Captures:\n" + print_array(a, (i => i.toString()), group_to_string) + "\n";
    s += "Named captures:\n" + print_object(a?.groups, group_to_string, "\tNone") + "\n";
    s += "Indices:\n" + print_array(a?.indices, (i => i.toString()), range_to_string, "\tNone") + "\n";
    s += "Named indices:\n" + print_object(a?.indices?.groups, range_to_string, "\tNone") + "\n";
    return s;
}

// Print the result of the exec function - an array exotic
function print_exec (result) {
    if (result == null) {
	    return "No match\n";
    }
    return (print_array_exotic(result));
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
        // const result = string.search(re);
        console.log("Not implemented")
    }
    if (frontend_func == "test") {
        // const result = re.test(string);
        console.log("Not implemented")
    }
    if (frontend_func == "match") {
        // const result = string.match(re);
        // const glob = /g/.test(flags); // checking if the g flag is present
        console.log("Not implemented")
    }
    if (frontend_func == "matchAll") {
        // const result = Array.from(string.matchAll(re));
        console.log("Not implemented")
    }
    return 0;
}

matcher();
