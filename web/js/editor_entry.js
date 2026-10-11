import { EditorView, drawSelection, keymap, lineNumbers } from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import {
  LRLanguage,
  LanguageSupport,
  HighlightStyle,
  syntaxHighlighting,
  bracketMatching,
} from "@codemirror/language";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { styleTags, tags as t } from "@lezer/highlight";
import { wast } from "@codemirror/lang-wast";
import { parser as miniml } from "./grammars/miniml.grammar.js";
import { parser as linlang } from "./grammars/linlang.grammar.js";
import { parser as richwasm } from "./grammars/richwasm.grammar.js";
import { Instruction, TypeConstructor } from "./grammars/richwasm.grammar.terms.js";
import { parser as pretty } from "./grammars/pretty.grammar.js";
import { classify } from "./grammars/richwasm_tokens.js";
import { locals } from "./locals.js";

const lineComment = { commentTokens: { line: ";" } };

function language(
  name,
  parser,
  styles,
  { languageData = lineComment, extensions = [], specializers = [] } = {},
) {
  return new LanguageSupport(
    LRLanguage.define({
      name,
      parser: parser.configure({ props: [styleTags(styles)], specializers }),
      languageData,
    }),
    extensions,
  );
}

const common = {
  Number: t.number,
  String: t.string,
  LineComment: t.lineComment,
  BlockComment: t.blockComment,
  "Colon Comma Separator": t.punctuation,
  "( )": t.paren,
};

const miniMl = language(
  "miniml",
  miniml,
  {
    ...common,
    Keyword: t.keyword,
    "Operator/Keyword": t.operator,
    "Int/... TypeVariable/... ProdType/... UProdType/... SumType/... USumType/... RecType/... RefType/... LinRefType/... FunType/... TypeParams/... TypeArgs/...":
      t.typeName,
  },
  {
    extensions: locals({
      scopes: new Set(["Let", "Split", "Fun", "Branch"]),
      topLevel: new Set(),
      lastWins: false,
    }),
  },
);

const linLang = language(
  "linlang",
  linlang,
  {
    ...common,
    Keyword: t.keyword,
    "Operator/Keyword": t.operator,
    "Definition/Keyword Variable/Keyword": t.variableName,
    "Int/... TypeVariable/... RefType/... ArrowType/... ProdType/... SumType/... RecType/... InfixType/...":
      t.typeName,
  },
  {
    extensions: locals({
      scopes: new Set(["Let", "Split", "Lam", "Case", "Function"]),
      topLevel: new Set(["Import", "Function"]),
      lastWins: true,
    }),
  },
);

const prettyRichWasm = language(
  "richwasm-pretty",
  pretty,
  { ...common, "Keyword Instruction": t.keyword, "Type/...": t.typeName, Atom: t.variableName },
  { languageData: {} },
);

function richWasm(constructors) {
  const classOf = new Map([
    ...constructors.types.map((c) => [c, TypeConstructor]),
    ...constructors.instructions.map((c) => [c, Instruction]),
  ]);
  return language(
    "richwasm",
    richwasm,
    {
      ...common,
      Instruction: t.keyword,
      TypeConstructor: t.typeName,
      Constructor: t.constant(t.name),
      "FieldName/Name": t.propertyName,
      Name: t.variableName,
    },
    { specializers: [{ from: classify, to: (value) => classOf.get(value) ?? -1 }] },
  );
}

/** Every color comes from the page's CSS variables, so style.css owns both themes. */
const theme = [
  EditorView.theme({
    "&": { color: "var(--fg)", backgroundColor: "var(--bg)", height: "100%" },
    ".cm-gutters": { color: "var(--muted)", backgroundColor: "var(--bg)", border: "none" },
    ".cm-content": { caretColor: "var(--fg)" },
    ".cm-cursor, .cm-dropCursor": { borderLeftColor: "var(--fg)" },
    "&.cm-focused .cm-selectionBackground, .cm-selectionBackground": {
      backgroundColor: "var(--selection)",
    },
    "&.cm-focused .cm-matchingBracket": { backgroundColor: "var(--selection)", outline: "none" },
    ".cm-activeLine, .cm-activeLineGutter": { backgroundColor: "transparent" },
    ".cm-local": { color: "var(--parameter)" },
    ".cm-toplevel": { color: "var(--function)" },
  }),
  syntaxHighlighting(
    HighlightStyle.define([
      { tag: t.keyword, color: "var(--keyword)" },
      { tag: t.typeName, color: "var(--type)" },
      { tag: t.number, color: "var(--number)" },
      { tag: t.string, color: "var(--string)" },
      { tag: t.propertyName, color: "var(--property)" },
      { tag: t.operator, color: "var(--operator)" },
      { tag: t.constant(t.name), color: "var(--number)" },
      { tag: t.punctuation, color: "var(--muted)" },
      { tag: [t.lineComment, t.blockComment], color: "var(--comment)" },
      { tag: t.paren, color: "var(--muted)" },
    ]),
  ),
];

function makeDoc(text, language, readOnly) {
  return {
    state: EditorState.create({
      doc: text,
      extensions: [
        lineNumbers(),
        drawSelection(),
        history(),
        bracketMatching(),
        keymap.of([...defaultKeymap, ...historyKeymap]),
        theme,
        language,
        EditorState.readOnly.of(readOnly),
        EditorView.editable.of(!readOnly),
      ],
    }),
    value() {
      return this.state.doc.toString();
    },
  };
}

function createView(parent) {
  let current = null;
  const listeners = [];
  const view = new EditorView({
    parent,
    dispatchTransactions(trs, view) {
      view.update(trs);
      if (current === null) return;
      current.state = view.state;
      if (trs.some((tr) => tr.docChanged)) listeners.forEach((f) => f(current));
    },
  });
  return {
    open(doc) {
      current = doc;
      view.setState(doc.state);
    },
    onChange: (f) => listeners.push(f),
  };
}

globalThis.richwasmEditor = {
  miniml: miniMl,
  linlang: linLang,
  pretty: prettyRichWasm,
  richWasm,
  wast: wast(),
  plain: [],
  makeDoc,
  createView,
};

const page = document.createElement("script");
page.src = "./page.bc.js";
document.body.appendChild(page);
