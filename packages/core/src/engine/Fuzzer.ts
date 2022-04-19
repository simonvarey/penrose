import { Queue } from "@datastructures-js/queue";
import { examples, registry } from "@penrose/examples";
import {
  genCode,
  makeGraph,
  primaryGraph,
  secondaryGraph,
} from "engine/Autodiff";
import * as fs from "fs";
import * as graphlib from "graphlib";
import { compileTrio, prepareState, resample, showError } from "index";
import * as ad from "types/ad";
import { VarAD } from "types/ad";
import { safe } from "utils/Util";

const stringifyNode = (node: ad.Node, inputs: number[]): string => {
  let obj: any = node;
  if (typeof node !== "number" && node.tag === "Input") {
    obj = { ...obj, val: inputs[node.index] };
  }
  return JSON.stringify(obj);
};

const stringifyGraph = (
  { graph, primary }: ad.Graph,
  inputs: number[]
): string => {
  const [node0, ...nodes] = graph.nodes();
  const strings = [
    `{\n  "primary": ${JSON.stringify(
      primary
    )},\n  "nodes": {\n    ${JSON.stringify(node0)}: ${stringifyNode(
      graph.node(node0),
      inputs
    )}`,
  ];
  for (const id of nodes) {
    strings.push(
      `,\n    ${JSON.stringify(id)}: ${stringifyNode(graph.node(id), inputs)}`
    );
  }

  const [edge0, ...edges] = graph.edges();
  strings.push(`\n  },\n  "edges": [\n    ${JSON.stringify(edge0)}`);
  for (const edge of edges) {
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
  const {
    params: { energyGraph },
  } = resample(await prepareState(res.value));

  const g1 = secondaryGraph([energyGraph]);
  const pairs = [...g1.nodes.entries()];

  const inputs = [];
  for (const [v] of pairs) {
    if (typeof v !== "number" && v.tag === "Input") {
      inputs[v.index] = v.val;
    }
  }

  fs.writeFileSync(
    "graph.json",
    stringifyGraph(
      { ...g1, primary: safe(g1.nodes.get(energyGraph), ":(") },
      inputs
    ),
    "utf8"
  );

  const g2 = makeGraph({
    primary: energyGraph,
    secondary: pairs.map(([v]) => v),
  });
  const f = genCode(g2);

  const outputs = f(inputs);

  const secondary = Object.fromEntries(
    pairs.map(([, id], i) => {
      const x = outputs.secondary[i];
      return [id, typeof x === "boolean" ? (x ? 1 : 0) : x];
    })
  );
  fs.writeFileSync(
    "outputs.json",
    `${JSON.stringify(
      {
        gradient: outputs.gradient.slice(1),
        primary: outputs.primary,
        secondary,
      },
      null,
      2
    )}\n`,
    "utf8"
  );
};

const getGraph = (): graphlib.Graph => {
  const graph = new graphlib.Graph({ multigraph: true });
  const { nodes, edges } = JSON.parse(fs.readFileSync("graph.json", "utf8"));
  for (const [id, node] of Object.entries(nodes)) {
    graph.setNode(id, node);
  }
  for (const { v, w, name } of edges) {
    graph.setEdge(v, w, undefined, name);
  }
  return graph;
};

export const layers = (): void => {
  const graph = getGraph();

  const depths = new Map<string, number>();
  const queue = new Queue<{ id: string; depth: number }>();
  for (const id of graph.sources()) {
    queue.enqueue({ id, depth: 0 });
  }
  while (!queue.isEmpty()) {
    const { id, depth } = queue.dequeue();
    depths.set(id, depth);
    const parents = graph.successors(id);
    if (!Array.isArray(parents)) {
      throw Error(":(");
    }
    parents: for (const parent of parents) {
      if (!depths.has(parent)) {
        const siblings = graph.predecessors(parent);
        if (!Array.isArray(siblings)) {
          throw Error(":(");
        }
        const siblingDepths = [];
        for (const sibling of siblings) {
          const siblingDepth = depths.get(sibling);
          if (siblingDepth === undefined) {
            continue parents;
          } else {
            siblingDepths.push(siblingDepth);
          }
        }
        queue.enqueue({ id: parent, depth: Math.max(...siblingDepths) + 1 });
      }
    }
  }

  const layers: string[][] = [];
  for (const [id, depth] of depths) {
    if (!(depth in layers)) {
      layers[depth] = [];
    }
    layers[depth].push(id);
  }
  fs.writeFileSync(
    "layers.json",
    `${JSON.stringify(layers, null, 2)}\n`,
    "utf8"
  );
};

const naryEdgeToIndex = (name: ad.NaryEdge) => parseInt(name, 10);

const translate = (node: ad.Node, children: Map<ad.Edge, VarAD>): VarAD => {
  if (typeof node === "number") {
    return node;
  }
  const { tag } = node;
  switch (tag) {
    case "Input": {
      const { index, val } = node as ad.Input; // HACK
      return { tag, index, val };
    }
    case "Unary": {
      const { unop } = node;
      return { tag, unop, param: safe(children.get(undefined), ":(") };
    }
    case "Binary": {
      const { binop } = node;
      return {
        tag,
        binop,
        left: safe(children.get("left"), ":("),
        right: safe(children.get("right"), ":("),
      };
    }
    case "Ternary": {
      return {
        tag,
        cond: safe(children.get("cond"), ":("),
        then: safe(children.get("then"), ":("),
        els: safe(children.get("els"), ":("),
      };
    }
    case "Nary": {
      const { op } = node;
      const params: VarAD[] = [];
      for (const [i, v] of children) {
        params[naryEdgeToIndex(i as ad.NaryEdge)] = v;
      }
      return { tag, op, params };
    }
    case "Debug": {
      const { info } = node;
      return { tag, info, node: safe(children.get(undefined), ":(") };
    }
  }
};

export const gradients = (): void => {
  const graph = getGraph();
  const varADs = new Map<string, VarAD>();
  const inputs = [];
  for (const id of graphlib.alg.topsort(graph)) {
    const edges = graph.inEdges(id);
    if (!Array.isArray(edges)) {
      throw Error(":(");
    }
    const v = translate(
      graph.node(id),
      new Map(
        edges.map(({ v, name }) => [name as ad.Edge, safe(varADs.get(v), ":(")])
      )
    );
    varADs.set(id, v);
    if (typeof v !== "number" && v.tag === "Input") {
      inputs[v.index] = v.val;
    }
  }
  for (const [id, v] of varADs) {
    const g = primaryGraph(v);
    const f = genCode(g);
    const outputs = f(inputs);
    const { gradient } = outputs;
    fs.writeFileSync(
      `outputs/${id}.json`,
      `${JSON.stringify(
        {
          ...outputs,
          gradient: inputs.map((x, i) => (i in gradient ? gradient[i] : 0)),
        },
        null,
        2
      )}\n`
    );
  }
};
