unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32
{
    let mut result = 0;
    let mut i = 0;
    loop {
        if i == count {
            break;
        }
        if *p1.add(i) < *p2.add(i) {
            result = -1;
            break;
        }
        if *p1.add(i) > *p2.add(i) {
            result = 1;
            break;
        }
        i += 1;
    }
    result
}
