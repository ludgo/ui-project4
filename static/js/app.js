var step_count;
var MAX_STEPS = 1000;
var facts = null;
var rules = null;



function resetOutput() {
	$(".textarea__output").val("");
	step_count = 0;
};

// update textarea with current fact set
function showFacts() {
	text = "";
	facts.forEach( function(fact) {
		text = text.concat(fact);
		text = text.concat("\n");
	});
	$('#textarea__facts').val(text);
};

// join string array on comma
function concatComma(arr){
	text = "";
	for (i=0; i<arr.length; i++) {
		text = text.concat(arr[i]);
		if (i===arr.length-1) {
			text = text.concat("\n");
		}
		else {
			text = text.concat(",");
		}
	}
	return text;
};

// update textarea with current rule set
function showRules() {
	text = "";
	Object.keys(rules).forEach( function(rule) {
		text = text.concat(rule);
		text = text.concat("\nIF ");
		text = text.concat(concatComma(rules[rule]["IF"]));
		text = text.concat("THEN ");
		text = text.concat(concatComma(rules[rule]["THEN"]));
		text = text.concat("\n");
	});
	$('#textarea__rules').val(text);
};

// append debug message to textarea
function showDebug(message) {
	text = "";
	text = text.concat($('#textarea__debug').val());
	text = text.concat(message);
	text = text.concat("\n");
	$('#textarea__debug').val(text);
};

// append message to textarea
function showMessage(message) {
	text = "";
	text = text.concat($('#textarea__messages').val());
	text = text.concat(message);
	text = text.concat("\n");
	$('#textarea__messages').val(text);
};



// make default loaded rules current rules
function defaultRules() {
	rules = JSON.parse(JSON.stringify(r));
	showRules();
	resetOutput();
};

// make default loaded facts current facts
function defaultFacts() {
	facts = JSON.parse(JSON.stringify(f));
	showFacts();
	resetOutput();
};

// make user input facts current facts and reset progress
function loadFacts() {
	text = "";
	text = text.concat($('#textarea__facts').val());
	facts = text.split('\n').filter(Boolean);
	resetOutput();
};

// add fact to current fact set
function addFact(fact) {
	facts.push(fact);
};

// remove fact to current fact set if exists
function removeFact(fact) {
	index = facts.indexOf(fact);
	if (index != -1) {
		facts.splice(index, 1);
	}
};

// check if fact in current fact set
function inFacts(statement) {
	for (i=0; i<facts.length; i++) {
		if (statement === facts[i]) {
			return true;
		}
	}
	return false;
};



// evaluate { statement } within string returning equivalent string containing results
function evalStr(str) {
	arr = str.split(/{|}/);
	arr.forEach( function(item, index) {
		if (index % 2 === 1) {
			arr[index] = eval('('.concat(arr[index]).concat(')'));
		}
	});
	return arr.join('');
};

// combine all facts with rules constructing possible consequences
function matchRules() {
	showDebug("MATCHES:");
	consequences = [];

	// split facts to parts
	fact_parts = [];
	facts.forEach( function(fact) {
		fact_parts.push(fact.split(' '));
	});
	
	// for each rule
	Object.keys(rules).forEach( function(rule) {
		// split rule conditions to parts
		condition_parts = [];
		rules[rule]["IF"].forEach( function(condition) {
			condition_parts.push(condition.split(' '));
		});

		// find all possible combinations
		possibilities = [];
		not_same = [];
		condition_parts.forEach( function(condition_part) {
			// skip special rule
			if (condition_part[0] === "<>") {
				not_same.push([condition_part[1], condition_part[2]]);
				return; // means continue forEach
			}

			// push always apart from spacial condition
			possibilities.push([]);

			// identify variables for single condition
			vars = {}
			for (i=0; i<condition_part.length; i++) {
				if (condition_part[i][0] === '?'&& !(condition_part[i] in vars)) {
					vars[condition_part[i]] = null;
				}
			}

			fact_parts.forEach( function(fact_part) {
				// check same length
				if (fact_part.length != condition_part.length) {
					return; // means continue forEach
				}
				// check same words excluding variables
				for (i=0; i<condition_part.length; i++) {
					if (fact_part[i] != condition_part[i] && condition_part[i][0] != '?') {
						return; // means continue forEach
					}
				}
				copy_vars = JSON.parse(JSON.stringify(vars));
				for (i=0; i<condition_part.length; i++) {
					if (condition_part[i][0] === '?') {
						// only single value for single variable
						if (copy_vars[condition_part[i]] != null && copy_vars[condition_part[i]] != fact_part[i]) {
							return; // means continue forEach
						}
						// find possible value for variable
						if (copy_vars[condition_part[i]] === null) {
							copy_vars[condition_part[i]] = fact_part[i];
						}
					}
				}
				possibilities[possibilities.length - 1].push(copy_vars);
			});
		});
		// all possible partial condition matches for single rule found here

		// all conditions must contain at least one possibility
		for (i=0; i<possibilities.length; i++) {
			if (!possibilities[i].length) {
				return; // means continue forEach
			}
		}

		// shirk array by pairing combinations until all total combinations found
		while (possibilities.length > 1) {
			// each iteration combines two array items
			pos_1 = possibilities.pop();
			pos_2 = possibilities.pop();
			// combine 2
			pos_comb = [];
			for (i=0; i<pos_1.length; i++) {
				for (j=0; j<pos_2.length; j++) {
					comb = JSON.parse(JSON.stringify(pos_1[i]));
					boo_add = true;
					Object.keys(pos_2[j]).forEach( function(key) {
						// find value for variable
						if (!(key in comb)) {
							comb[key] = pos_2[j][key];
						}
						// single variable cannot have multiple different values
						else if (comb[key] != pos_2[j][key]) {
							boo_add = false;
						}
					});
					if (boo_add) {
						pos_comb.push(comb);
					}
				}
			}
			// push back 1 only
			if (pos_comb.length) {
				possibilities.push(pos_comb);
			}
		}
		// all full rule statement identified here
		if (!possibilities.length) {
			return; // means continue forEach
		}

		// start reasoning based on found matches
		consequencesStr = JSON.stringify(rules[rule]["THEN"]);

		possibilities[0].forEach( function(possibility) {
			// check special condition
			for (i=0; i<not_same.length; i++) {
				if (possibility[not_same[i][0]] === possibility[not_same[i][1]]) {
					return; // means continue forEach
				}
			}
			// find possible consequence matches
			matchStr = consequencesStr;
			Object.keys(possibility).forEach( function(key) {
				matchStr = matchStr.split(key).join(possibility[key])
			});
			// check all variables have been replaced
			if (matchStr.indexOf('?') === -1) {
				// statements may contain evaluation
				matchStr = evalStr(matchStr);
				match = JSON.parse(matchStr);
				consequences.push(match);
				showDebug(rule);
				showDebug(match);
			}
		});
		// a single rule possible consequences with respect to facts found here
	});
	// all possible consequences with respect to rules and facts found here

	return consequences;
};

// return applicable consequences only
function removeRedundant(consequences) {
	showDebug("APPLICABLE:");
	applicableConsequences = [];
	consequences.forEach( function(consequence) {
		modify_count = 0;
		consequence.forEach( function(consequence_part) {
			arr = consequence_part.split(' ');
			action = arr[0];
			arr.shift();
			cons = arr.join(' ');
			if (action === "add") {
				if (!inFacts(cons)) {
					// can be added
					modify_count++;
				}
			}
			else if (action === "delete") {
				if (inFacts(cons)) {
					// can be deleted
					modify_count++;
				}
			}
		});
		if (modify_count > 0) {
			// would modify fact set thus is applicable
			applicableConsequences.push(consequence)
			showDebug(consequence);
		}
	});
	return applicableConsequences;
};

// take single rule application and perform all resulting actions
function apply(consequence) {
	showDebug("APPLIED:");
	showDebug(consequence);
	consequence.forEach( function(consequence_part) {
		arr = consequence_part.split(' ');
		action = arr[0];
		arr.shift();
		statement = arr.join(' ');
		if (action === "add") {
			if (!inFacts(statement)) {
				addFact(statement);
			}
		}
		else if (action === "delete") {
			if (inFacts(statement)) {
				removeFact(statement);
			}
		}
		else if (action === "message") {
			showMessage(statement);
		}
	});
};

// single system step with realization of max. 1 consequence only
function step() {
	if (step_count >= MAX_STEPS) {
		return false;
	}
	step_count++;
	showDebug("STEP ".concat(step_count));

	applicableConsequences = removeRedundant(matchRules());
	if (applicableConsequences.length) {
		// only single rule match can be used within single step
		apply(applicableConsequences[0]);
		showFacts();
		showDebug("");
		return true;
	}
	showDebug("\n! END");
	step_count = MAX_STEPS;
	return false;
};

// perform all system steps
function run() {
	while (step());
};



$(function() {
	// facts
	defaultFacts();
	$('#button__default').bind('click', defaultFacts);
	$('#button__load').bind('click', loadFacts);
	// rules
	defaultRules();
	$('#button__rules').bind('click', defaultRules);
	// program
	$('#button__step').bind('click', step);
	$('#button__run').bind('click', run);
});
