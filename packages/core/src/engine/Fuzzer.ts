import { Queue } from "@datastructures-js/queue";
import { examples, registry } from "@penrose/examples";
import * as fs from "fs";
import { compileTrio, prepareState, showError } from "index";
import { VarAD } from "types/ad";
import { safe } from "utils/Util";

export type Node =
  | ConstNode
  | InputNode
  | UnaryNode
  | BinaryNode
  | TernaryNode
  | NaryNode
  | DebugNode;

export type ConstNode = number;

export interface InputNode {
  tag: "Input";
  index: number;
  val: number;
}

export interface UnaryNode {
  tag: "Unary";
  unop:
    | "neg"
    | "squared"
    | "sqrt"
    | "inverse"
    | "abs"
    | "acosh"
    | "acos"
    | "asin"
    | "asinh"
    | "atan"
    | "atanh"
    | "cbrt"
    | "ceil"
    | "cos"
    | "cosh"
    | "exp"
    | "expm1"
    | "floor"
    | "log"
    | "log2"
    | "log10"
    | "log1p"
    | "round"
    | "sign"
    | "sin"
    | "sinh"
    | "tan"
    | "tanh"
    | "trunc";
}

export interface BinaryNode {
  tag: "Binary";
  binop:
    | "+"
    | "*"
    | "-"
    | "/"
    | "max"
    | "min"
    | "atan2"
    | "pow"
    | ">"
    | "<"
    | "==="
    | "&&"
    | "||";
}

export interface TernaryNode {
  tag: "Ternary";
}

export interface NaryNode {
  tag: "Nary";
  op: "addN" | "maxN" | "minN";
}

export interface DebugNode {
  tag: "Debug";
  info: string;
}

export type Edge = UnaryEdge | BinaryEdge | TernaryEdge | NaryEdge | DebugEdge;
export type UnaryEdge = undefined;
export type BinaryEdge = "left" | "right";
export type TernaryEdge = "cond" | "then" | "els";
export type NaryEdge = `${number}`;
export type DebugEdge = undefined;

type Id = `_${number}`;

const indexToID = (index: number): Id => `_${index}`;

const indexToNaryEdge = (index: number): NaryEdge => `${index}`;

interface Child {
  child: VarAD;
  name: Edge;
}

const translate = (v: VarAD): { node: Node; children: Child[] } => {
  const { val, op, isInput, childrenAD, index } = v;
  const naryChildren: Child[] = childrenAD.map(({ node }, i) => ({
    child: node,
    name: indexToNaryEdge(i),
  }));
  if (op === "max list") {
    return { node: { tag: "Nary", op: "maxN" }, children: naryChildren };
  } else if (op === "min list") {
    return { node: { tag: "Nary", op: "minN" }, children: naryChildren };
  } else if (op === "+ list") {
    return { node: { tag: "Nary", op: "addN" }, children: naryChildren };
  } else if (childrenAD.length === 0) {
    if (isInput) {
      return { node: { tag: "Input", index: index + 1, val }, children: [] };
    } else {
      throw Error(":(");
    }
  } else if (childrenAD.length === 1) {
    const [{ node: child }] = childrenAD;
    const children = [{ child, name: undefined }];
    if (
      op === "squared" ||
      op === "cos" ||
      op === "sin" ||
      op === "sqrt" ||
      op === "abs"
    ) {
      return { node: { tag: "Unary", unop: op }, children };
    } else if (op === "- (unary)") {
      return { node: { tag: "Unary", unop: "neg" }, children };
    } else {
      throw Error(":(");
    }
  } else if (childrenAD.length === 2) {
    const [{ node: left }, { node: right }] = childrenAD;
    const children: Child[] = [
      { child: left, name: "left" },
      { child: right, name: "right" },
    ];
    if (
      op === "+" ||
      op === "*" ||
      op === "-" ||
      op === "max" ||
      op === "/" ||
      op === "min"
    ) {
      return { node: { tag: "Binary", binop: op }, children };
    } else if (op === "lt") {
      return { node: { tag: "Binary", binop: "<" }, children };
    } else {
      throw Error(":(");
    }
  } else if (childrenAD.length === 3) {
    const [{ node: cond }, { node: then }, { node: els }] = childrenAD;
    if (op === "ifCond") {
      return {
        node: { tag: "Ternary" },
        children: [
          { child: cond, name: "cond" },
          { child: then, name: "then" },
          { child: els, name: "els" },
        ],
      };
    } else {
      throw Error(":(");
    }
  } else {
    throw Error(":(");
  }
};

const stringifyGraph = (
  primary: Id,
  nodes: [Id, Node][],
  edges: { v: Id; w: Id; name?: Edge }[]
): string => {
  const [id0, node0] = nodes[0];
  const strings = [
    `{\n  "primary": ${JSON.stringify(
      primary
    )},\n  "nodes": {\n    ${JSON.stringify(id0)}: ${JSON.stringify(node0)}`,
  ];
  for (const [id, node] of nodes.slice(1)) {
    strings.push(`,\n    ${JSON.stringify(id)}: ${JSON.stringify(node)}`);
  }

  strings.push(`\n  },\n  "edges": [\n    ${JSON.stringify(edges[0])}`);
  for (const edge of edges.slice(1)) {
    strings.push(`,\n    ${JSON.stringify(edge)}`);
  }
  strings.push("\n  ]\n}\n");

  return strings.join("");
};

export const fuzz = async (): Promise<void> => {
  const setTheory = examples["set-theory-domain"];
  const dslSet = setTheory["setTheory.dsl"];
  const styVenn = setTheory["venn.sty"];
  const subTree = setTheory["tree.sub"];
  const variation = safe(
    registry.trios.find(
      ({ substance, style }) => substance === "tree" && style === "venn"
    ),
    "tree-venn should exist"
  ).variation;

  const res = compileTrio({
    substance: subTree,
    style: styVenn,
    domain: dslSet,
    variation,
  });
  if (!res.isOk()) {
    throw Error(showError(res.error));
  }

  // resample because initial sampling did not use the special sampling seed
  const { params } = await prepareState(res.value);

  const constants = new Map<number, Id>();
  const ids = new Map<VarAD, Id>();
  const nodes = new Map<Id, Node>();
  const queue = new Queue([params.energyGraph]);
  const edges: [Child, VarAD][] = [];
  while (!queue.isEmpty()) {
    const v = queue.dequeue();
    if (!v.op.endsWith(" list") && v.childrenAD.length === 0 && !v.isInput) {
      let id = constants.get(v.val);
      if (id === undefined) {
        id = indexToID(nodes.size);
        constants.set(v.val, id);
        nodes.set(id, v.val);
      }
      ids.set(v, id);
    } else if (!ids.has(v)) {
      const id = indexToID(nodes.size);
      ids.set(v, id);
      const { node, children } = translate(v);
      nodes.set(id, node);
      for (const edge of children) {
        edges.push([edge, v]);
        queue.enqueue(edge.child);
      }
    }
  }

  fs.writeFileSync(
    "graph.json",
    stringifyGraph(
      safe(ids.get(params.energyGraph), ":("),
      [...nodes.entries()],
      edges.map(([{ child, name }, parent]) => ({
        v: safe(ids.get(child), ":("),
        w: safe(ids.get(parent), ":("),
        name,
      }))
    ),
    "utf8"
  );

  const secondary = [];
  for (const [{ val }, id] of ids) {
    secondary.push([id, val]);
  }
  fs.writeFileSync(
    "outputs.json",
    `${JSON.stringify(
      {
        gradient: params.currGradient(params.xsVars.map(({ val }) => val)),
        primary: params.energyGraph.val,
        secondary: Object.fromEntries(secondary),
      },
      null,
      2
    )}\n`,
    "utf8"
  );
};
