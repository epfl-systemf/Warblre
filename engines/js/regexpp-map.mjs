/** From https://github.com/Ef55/regexpp-map */
/**
 * The visitor to map an AST.
 */
export class RegExpMapper {
    /**
     * Initialize this visitor.
     * @param handlers Callbacks for each node.
     */
    constructor(handlers) {
        this._handlers = handlers;
    }
    /**
     * Visit a given node and descendant nodes.
     * @param node The root node to visit tree.
     */
    // eslint-disable-next-line complexity
    visit(node) {
        switch (node.type) {
            case "Alternative":
                return this.visitAlternative(node);
            case "Assertion":
                return this.visitAssertion(node);
            case "Backreference":
                return this.visitBackreference(node);
            case "CapturingGroup":
                return this.visitCapturingGroup(node);
            case "Character":
                return this.visitCharacter(node);
            case "CharacterClass":
                return this.visitCharacterClass(node);
            case "CharacterClassRange":
                return this.visitCharacterClassRange(node);
            case "CharacterSet":
                return this.visitCharacterSet(node);
            case "ClassIntersection":
                return this.visitClassIntersection(node);
            case "ClassStringDisjunction":
                return this.visitClassStringDisjunction(node);
            case "ClassSubtraction":
                return this.visitClassSubtraction(node);
            case "ExpressionCharacterClass":
                return this.visitExpressionCharacterClass(node);
            case "Group":
                return this.visitGroup(node);
            case "Pattern":
                return this.visitPattern(node);
            case "Quantifier":
                return this.visitQuantifier(node);
            case "RegExpLiteral":
                return this.visitRegExpLiteral(node);
            case "StringAlternative":
                return this.visitStringAlternative(node);
            default:
                throw new Error(`Unknown type: ${node.type}`);
        }
    }
    visitRange(node) {
        switch (node.type) {
            case "Character":
                return this.visitClassCharacter(node);
            case "CharacterClassRange":
                return this.visitClassCharacterClassRange(node);
            case "CharacterSet":
                return this.visitClassCharacterSet(node);
        }
    }
    visitSet(node) {
        switch (node.type) {
            case "Character":
                return this.visitClassCharacter(node);
            case "CharacterClassRange":
                return this.visitClassCharacterClassRange(node);
            case "CharacterSet":
                return this.visitClassCharacterSet(node);
            // case "CharacterClass":
            //     return this.visitClassCharacterClass(node);
            // case "ClassStringDisjunction":
            //     return this.visitClassClassStringDisjunction(node);
            // case "ExpressionCharacterClass":
            //     return this.visitClassExpressionCharacterClass(node);
            default:
                throw new Error(`Unicode sets (v flag) not yet supported: ${node.type}`);
        }
    }
    // Regexes
    visitAlternative(node) {
        let elements = node.elements.map(alternative => this.visit(alternative));
        return this._handlers.onAlternative(node, elements);
    }
    visitAssertion(node) {
        if (node.kind === "lookahead" || node.kind === "lookbehind") {
            let alternatives = node.alternatives.map(alternative => this.visit(alternative));
            return this._handlers.onLookaroundAssertion(node, alternatives);
        }
        else {
            return this._handlers.onBoundaryAssertion(node);
        }
    }
    visitBackreference(node) {
        return this._handlers.onBackreference(node);
    }
    visitCapturingGroup(node) {
        let alternatives = node.alternatives.map(alternative => this.visit(alternative));
        return this._handlers.onCapturingGroup(node, alternatives);
    }
    visitCharacter(node) {
        return this._handlers.onCharacter(node);
    }
    visitCharacterClass(node) {
        if (node.unicodeSets) {
            let elements = node.elements.map(element => this.visitSet(element));
            return this._handlers.onCharacterClass(node, elements);
        }
        else {
            let elements = node.elements.map(element => this.visitRange(element));
            return this._handlers.onCharacterClass(node, elements);
        }
    }
    visitCharacterClassRange(node) {
        let min = this.visit(node.min);
        let max = this.visit(node.max);
        return this._handlers.onCharacterClassRange(node, min, max);
    }
    visitCharacterSet(node) {
        return this._handlers.onCharacterSet(node);
    }
    visitClassIntersection(node) {
        let l = this.visit(node.left);
        let r = this.visit(node.right);
        return this._handlers.onClassIntersection(node, l, r);
    }
    visitClassStringDisjunction(node) {
        let alternatives = node.alternatives.map(alternative => this.visitStringAlternative(alternative));
        return this._handlers.onClassStringDisjunction(node, alternatives);
    }
    visitClassSubtraction(node) {
        let l = this.visit(node.left);
        let r = this.visit(node.right);
        return this._handlers.onClassSubtraction(node, l, r);
    }
    visitExpressionCharacterClass(node) {
        return this._handlers.onExpressionCharacterClass(node, this.visit(node.expression));
    }
    visitGroup(node) {
        let alternatives = node.alternatives.map(alternative => this.visitAlternative(alternative));
        return this._handlers.onGroup(node, alternatives);
    }
    visitPattern(node) {
        let alternatives = node.alternatives.map(alternative => this.visitAlternative(alternative));
        return this._handlers.onPattern(node, alternatives);
    }
    visitQuantifier(node) {
        return this._handlers.onQuantifier(node, this.visit(node.element));
    }
    visitRegExpLiteral(node) {
        let pattern = this.visitPattern(node.pattern);
        return this._handlers.onRegExpLiteral(node, pattern);
    }
    visitStringAlternative(node) {
        let elements = node.elements.map(element => this.visitCharacter(element));
        return this._handlers.onStringAlternative(node, elements);
    }
    // Character classes
    visitClassCharacter(node) {
        return this._handlers.onRangeCharacter(node);
    }
    visitClassCharacterClassRange(node) {
        return this._handlers.onRangeCharacterClassRange(node);
    }
    visitClassCharacterSet(node) {
        return this._handlers.onRangeCharacterSet(node);
    }
}
(function (RegExpMapper) {
    function map(r, onAlternative, onBoundaryAssertion, onLookaroundAssertion, onBackreference, onCapturingGroup, onCharacter, onCharacterClass, onCharacterClassRange, onCharacterSet, onClassIntersection, onClassStringDisjunction, onClassSubtraction, onExpressionCharacterClass, onGroup, onPattern, onQuantifier, onRegExpLiteral, onStringAlternative, onRangeCharacter, onRangeCharacterClassRange, onRangeCharacterSet) {
        return new RegExpMapper({
            onAlternative,
            onBoundaryAssertion,
            onLookaroundAssertion,
            onBackreference,
            onCapturingGroup,
            onCharacter,
            onCharacterClass,
            onCharacterClassRange,
            onCharacterSet,
            onClassIntersection,
            onClassStringDisjunction,
            onClassSubtraction,
            onExpressionCharacterClass,
            onGroup,
            onPattern,
            onQuantifier,
            onRegExpLiteral,
            onStringAlternative,
            onRangeCharacter,
            onRangeCharacterClassRange,
            onRangeCharacterSet,
        }).visit(r);
    }
    RegExpMapper.map = map;
})(RegExpMapper || (RegExpMapper = {}));
