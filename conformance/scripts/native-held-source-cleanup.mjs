// Held-source cleanup regression, not a formal JS refinement witness.
// Usage: node conformance/scripts/native-held-source-cleanup.mjs /absolute/path/to/js-repo
import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { setImmediate as turn } from 'node:timers/promises';
import { pathToFileURL } from 'node:url';

assert(process.argv[2], 'Pass the built graphql-incremental-delivery-js repository path.');
const runtime = resolve(process.argv[2]);
assert.equal(process.argv.length, 3, 'Pass exactly one built runtime repository path.');
// Use the pinned GraphQL 17 ESM entry, matching the native library's own imports.
// Mixing its CJS and ESM schema objects would invalidate the diagnostic.
const graphql = await import(pathToFileURL(resolve(runtime, 'node_modules/graphql/index.mjs')));
const { graphqlIncrementally } = await import(pathToFileURL(resolve(runtime, 'dist/esm/index.js')));
const { IncrementalExecutor } = await import(
  pathToFileURL(resolve(runtime, 'dist/esm/IncrementalExecutor.js')),
);

const counters = { acquired: 0, built: 0, cancelled: 0, pulls: 0, returned: 0 };
const original = IncrementalExecutor.prototype.buildStreamItemQueue;
IncrementalExecutor.prototype.buildStreamItemQueue = function (...args) {
  counters.built++;
  const stream = original.apply(this, args);
  const cancel = stream.cancel;
  return { ...stream, cancel(reason) { counters.cancelled++; return cancel(reason); } };
};

function gate() {
  let reject;
  const promise = new Promise((_, no) => { reject = no; });
  return { promise, reject };
}

const g = gate(), h = gate();
const values = {
  [Symbol.asyncIterator]() {
    counters.acquired++;
    return {
      next() { counters.pulls++; return Promise.resolve({ done: true }); },
      return() { counters.returned++; return Promise.resolve({ done: true }); },
    };
  },
};
const result = await graphqlIncrementally({
  schema: graphql.buildSchema(`
    type Query { box: Box badG: String! badH: String! }
    type Box { values: [String] dummy: String }
  `),
  source: `{
    ... @defer(label: "G") { box { values @stream(initialCount: 0) } badG }
    ... @defer(label: "H") { box { dummy } badH }
  }`,
  rootValue: { box: { values, dummy: 'ok' }, badG: () => g.promise, badH: () => h.promise },
  enableEarlyExecution: false,
});
assert(result.subsequentResults, JSON.stringify(result));
const first = result.subsequentResults.next();
await turn();
assert.deepEqual(counters, { acquired: 1, built: 1, cancelled: 0, pulls: 0, returned: 0 });
g.reject(Error('G failed'));
const firstUpdate = await first;
assert.equal(firstUpdate.value.hasNext, true);
assert.equal(firstUpdate.value.completed[0].errors[0].message, 'G failed');
const second = result.subsequentResults.next();
h.reject(Error('H failed'));
const secondUpdate = await second;
assert.equal(secondUpdate.value.hasNext, false);
assert.equal(secondUpdate.value.completed[0].errors[0].message, 'H failed');
assert.equal((await result.subsequentResults.next()).done, true);
await turn();
assert.deepEqual(counters, { acquired: 1, built: 1, cancelled: 1, pulls: 0, returned: 1 });
console.log('Validated generated query disposed its acquired held source exactly once.');
console.log(JSON.stringify(counters));
