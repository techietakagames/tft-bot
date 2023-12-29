import os
import discord
from dotenv import load_dotenv
import main


load_dotenv()
TOKEN = os.getenv('DISCORD_TOKEN')

client = discord.Client(intents=discord.Intents.default())

@client.event
async def on_ready():
    print(f'{client.user} has connected to Discord!')


@client.event
async def on_message(message):
    # Make sure the Bot doesn't respond to it's own messages
    if message.author == client.user:
        return
    if message.content != "" and message.channel.name != "tft-bot":
        await message.channel.send("Use `#tft-bot` channel so others can mute if desired")
        return
    print("Hit", str(message.content))
    print("HIT2", message.channel)

    if len(message.content) > 0:
        arr = message.content.strip().split()[1:]
        try:
            print("HERE")
            print(arr)

            result = await main.main(arr)
            print("HERE3")
            print(result)
            print("AGAIN")
            if result:
                await message.channel.send(result)
            else:
                parser = main.parse_options()
                help = parser.format_help()
                await message.channel.send(help)
            print("HERE2")

        except Exception as e:
            parser = main.parse_options()
            help = parser.format_help()
            await message.channel.send(help)




    # await client.process_commands(message)


client.run(TOKEN)
