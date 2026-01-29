// verifast_options{ignore_unwind_paths ignore_ref_creation}

#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
    where T: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

unsafe fn wait_for_pulse(_source: i32)
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
{
    println!("{}", n);
}


struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, source} = data;

    loop {
        wait_for_pulse(source);
        {
            let guard = (*counter).lock().unwrap();
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();
            drop(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
{
    let data = CountPulsesData { counter, source };
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let counter = Box::into_raw(Box::new(mutex));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let count;
            {
                let guard = (*counter).lock().unwrap();
                count = *(*counter).data_ptr();
                drop(guard);
            }
            print_u32(count);
        }
    }
}
