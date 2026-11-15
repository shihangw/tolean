import { file } from "./lib";
import { directory } from "./dir";
import { leaf } from "./leaf.js";
export function result(): bigint { return file() + directory() + leaf(); }
