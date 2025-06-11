# smolnes-nut

The [smolnes](https://github.com/binji/smolnes) NES emulator, crudely ported to Squirrel for Portal 2.

Make sure to check out [binji](https://github.com/binji)'s amazing work on the original 5KB emulator.

## Usage
**Note: This section documents how to interface with the emulator as a Squirrel library. For a playable Portal 2 demo, see the next section.**

1. Include `smolnes.nut` in any script environment (or just copy its code into your source file). Note that it currently creates many globals with short and common names (e.g. `A`, `X`, `Y`, `val`, `result`, `dot`, etc.), which may not be suitable in some already populated environments.
2. Call `smolnes_init(rom)`, where `rom` is an array of 8-bit values representing the cartridge ROM buffer.
3. Define a global `smolnes_render` function to act as a render handler. This step is technically optional, but you likely want your emulator to actually render frames. This function won't be passed any arguments, as the actual framebuffer is stored in the `frame_buffer` global as a 1-dimensional 256x240 pixel BGR565 array.
4. Call `smolnes_loop()` to simulate a CPU cycle. In most Squirrel environments, this can be attached to a simple `while(true)` loop. For Source engine timeout workarounds, see the Portal 2 demo code.
5. (Optional): Set the `pixel_skip` global to the amount of pixels you want to skip on both axes. This will leave "gaps" in the framebuffer, but allows for higher performance at a lower resolution.

## Example Demo

1. Clone this repository and move the `portal2_dlc3` folder from `examples` to your Portal 2 game files. If you already have a `_dlc3` folder there, rename this one to `_dlc4`.
2. Copy the `smolnes.nut` file from the root of this repository to `Portal 2/portal2_dlc3/scripts/vscripts`.
2. Start the game. You'll likely get a long loading screen that freezes once the dots become yellow. If you're on Windows, just restart the game. If you're on Linux, you'll have to use the developer console (usually the backtick key if enabled) to load a map.
3. Enter Triple Laser using the command `map sp_a2_triple_laser`. You will be placed in front of the screen and a few buttons. This example uses LJ65 as the example ROM, though it is admittedly impossible to play the game with the low resolution.
4. If you want to change the ROM, just follow the format of `lj65_rom.nut` - it's an array of hex bytes representing the ROM buffer. Note that only mapper 1 has been tested.
