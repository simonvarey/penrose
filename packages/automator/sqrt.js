(inputs) => {
  const _1 = inputs[0];
  const _3 = 1;
  const _5 = 2;
  const _7 = 0.00001;
  const _0 = Math.sqrt(_1);
  const _6 = Math.max(_7, _0);
  const _4 = _5 * _6;
  const _2 = _3 / _4;
  const _9 = _2 * _3;
  const _8 = _9;
  return { gradient: [_8], primary: _0, secondary: [] };
}
