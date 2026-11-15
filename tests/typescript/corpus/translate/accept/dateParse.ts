export function year(): number { return Date.parse("1970"); }
export function month(): number { return Date.parse("1970-02"); }
export function expanded(): number { return Date.parse("-000001-01-01"); }
export function midnight(): number { return Date.parse("2000-12-31T24:00:00.000Z"); }
export function offset(): number { return Date.parse("1970-01-01T00:00+01:30"); }
export function invalid(): number { return Date.parse("2000-13-01"); }
