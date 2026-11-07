// A value import of the enum: the file reads its members.
import { Status, pause } from "./status.ts";

interface Task {
  readonly name: string;
  readonly status: Status;
}

export function isOpen(t: Task): boolean {
  return t.status !== Status.Done;
}

export function paused(t: Task): Task {
  return { name: t.name, status: pause(t.status) };
}
