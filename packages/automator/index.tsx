require("global-jsdom/register");
import { fuzz } from "@penrose/core";

(async () => {
  fuzz();
})();
