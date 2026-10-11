import { Decoration, ViewPlugin } from "@codemirror/view";
import { syntaxTree } from "@codemirror/language";

const scopeMarks = {
  local: Decoration.mark({ class: "cm-local" }),
  module: Decoration.mark({ class: "cm-toplevel" }),
};

function lastSubform(node) {
  let child = node.lastChild;
  while (child && (child.name === ")" || child.name === "(" || child.type.isSkipped))
    child = child.prevSibling;
  return child;
}

/**
 * A `Definition` inside one of `scopes` binds over that form's last subform,
 * any other over the module; among one form's binders the first wins, unless
 * `lastWins`.
 */
export function locals({ scopes, topLevel, lastWins }) {
  const bodyOf = (definition) => {
    if (topLevel.has(definition.parent.name)) return null;
    for (let node = definition.parent; node; node = node.parent)
      if (scopes.has(node.name)) return lastSubform(node);
    return null;
  };
  const decorate = (state) => {
    const text = (node) => state.doc.sliceString(node.from, node.to);
    const definitions = [];
    const references = [];
    syntaxTree(state).iterate({
      enter: ({ node }) => {
        if (node.name === "Definition") {
          const body = bodyOf(node);
          definitions.push({
            node,
            name: text(node),
            mark: body ? scopeMarks.local : scopeMarks.module,
            from: body ? body.from : 0,
            to: body ? body.to : state.doc.length,
          });
        } else if (node.name === "Variable") references.push(node);
      },
    });
    const inner = (a, b) => {
      const sizeA = a.to - a.from;
      const sizeB = b.to - b.from;
      if (sizeA !== sizeB) return sizeA < sizeB ? a : b;
      return lastWins === a.node.from > b.node.from ? a : b;
    };
    const marks = definitions.map((d) => d.mark.range(d.node.from, d.node.to));
    for (const ref of references) {
      const name = text(ref);
      const binders = definitions.filter(
        (d) => d.name === name && d.from <= ref.from && ref.to <= d.to,
      );
      if (binders.length > 0) marks.push(binders.reduce(inner).mark.range(ref.from, ref.to));
    }
    return Decoration.set(marks, true);
  };
  return ViewPlugin.fromClass(
    class {
      constructor(view) {
        this.decorations = decorate(view.state);
      }
      update(update) {
        if (update.docChanged || syntaxTree(update.state) !== syntaxTree(update.startState))
          this.decorations = decorate(update.state);
      }
    },
    { decorations: (plugin) => plugin.decorations },
  );
}
