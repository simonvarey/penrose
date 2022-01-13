import {
  ICenter,
  IFill,
  INamed,
  IRect,
  IRotate,
  IShape,
  IString,
  IStroke,
} from "types/shapes";
import { IStrV } from "types/value";
import {
  Canvas,
  sampleColor,
  sampleNoPaint,
  sampleStroke,
  sampleVector,
  sampleZero,
  StrV,
} from "./Samplers";

export interface IText
  extends INamed,
    IStroke,
    IFill,
    ICenter, // the center of the bounding box of the text
    IRect,
    IRotate,
    IString {
  // TODO; pare down this set of attributes
  visibility: IStrV;
  fontFamily: IStrV;
  fontSizeAdjust: IStrV;
  fontStretch: IStrV;
  fontStyle: IStrV;
  fontVariant: IStrV;
  fontWeight: IStrV;
  textAnchor: IStrV;
  lineHeight: IStrV;
  alignmentBaseline: IStrV;
  dominantBaseline: IStrV;
}

export const sampleText = (canvas: Canvas): IText => ({
  name: StrV("defaultText"),
  style: StrV(""),
  strokeWidth: sampleStroke(),
  strokeStyle: StrV("solid"),
  strokeColor: sampleNoPaint(),
  strokeDashArray: StrV(""),
  fillColor: sampleColor(),
  center: sampleVector(canvas),
  width: sampleZero(),
  height: sampleZero(),
  rotation: sampleZero(),
  string: StrV("defaultText"),
  visibility: StrV(""),
  fontFamily: StrV("sans-serif"),
  fontSize: StrV("12pt"),
  fontSizeAdjust: StrV(""),
  fontStretch: StrV(""),
  fontStyle: StrV(""),
  fontVariant: StrV(""),
  fontWeight: StrV(""),
  lineHeight: StrV(""),
  textAnchor: StrV("middle"),
  // NOTE: both `alignmentBaseline` and `dominantBaseline` are necessary for browser support. For instance, Firefox only respects the latter.
  alignmentBaseline: StrV("middle"),
  dominantBaseline: StrV("middle"),
});

export type Text = IShape & { shapeType: "Text" } & IText;

export const makeText = (canvas: Canvas, properties: Partial<IText>): Text => ({
  ...sampleText(canvas),
  ...properties,
  shapeType: "Text",
});
